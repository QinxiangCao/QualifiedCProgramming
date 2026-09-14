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

/* ===========================================================================
   MiniSat solver contracts and verification scope.

   CONTRACT AND SCOPE.  The public contracts are stated once, in solver_qcp.h,
   and are not restated here: the call order, the per-return-code promises and
   the paper-to-port name map in its "CLIENT PROTOCOL" comment above the public
   interface, the meaning of every ghost name ON THE PUBLIC HEADER in the
   "GHOST-NAME LEGEND" beside it (the ghost names used only inside this file
   are glossed under GHOST STATE below), and each function's own Require/Ensure at its declaration.  In
   particular the fork after `solver_solve` returns `0` -- a further contracted
   call is available iff the exported state is watch-ready, and otherwise
   `cnf_unsat(n, F)` holds of the clause set itself and the verdict is final --
   is the `(solver_query_watch_ready(Mout) || cnf_unsat(n, F))` alternative on
   the `__return == 0` arm of `solver_solve_incremental_spec` there.  What this
   file adds: termination is not proved; a `-2` return reports learnt-clause or
   watcher-vector capacity exhaustion with no SAT/UNSAT verdict and no progress
   guarantee; and the trust/scope material below.

   After solve's `-2`, insertion and simplification restore a saved propagation
   cursor when the pending flag is set.  Their own `-2` continuation corollaries
   recover a base state with the original formula, seed, growth bounds and
   ownership; they do not promise progress or a drained queue.  Keep the framed
   watcher growth slack.  Retrying the original clause also requires a valid,
   owned saved or refilled input range, since insertion may mutate that range.
   Deletion, parser/I/O and optional configurations remain outside this scope;
   allocation failure is not covered by the success-assumed allocation contracts.

   GHOST STATE.  `msolver` is the abstract solver state threaded through every
   contract as the ghost `M` (and its per-phase variants, see NAMING below);
   `ms_core(M)` is its `mtrail` (assignment/level/reason trail),
   `ms_prob(M)`/`ms_learnt(M)` the original and learnt clause databases,
   `ms_stats(M)` the 11-counter statistics vector (see STATS TABLE), and
   `ms_model(M)`/`ms_size(M)` the externally observable model and variable
   count.  `solver_rep(s, M)` is the whole-struct footprint tying the C struct
   `s` to `M`.  Spatial views such as `solver_removable_frame_at` and
   `solver_analyze_frame` describe function-local memory; pure invariants
   such as `solver_propagation_inv` separately constrain the logical state.

   NAMING.  Ghost `msolver` binders are spelled `M` followed by a short tag
   for the point in execution they capture: `Mcur`/`Mnext` (before/after one
   step of the current loop), `Mdone`/`Mfinish` (a function's exit state),
   `Manalyze`/`Manalyzed`, `Mrecord`, `Mscan`, `Mprop`, `Mrestart`, `Mreduced`
   and similar name the phase of `solver_analyze` / `solver_record` /
   `solver_propagate` / `solver_solve` a state belongs to.  `Mact`/`Mtag`
   similarly name states reached mid-derivation inside one such phase.
   STATS TABLE.  `ms_stats(M) : list Z` is an 11-element counter vector; every
   annotation reads it through a named accessor (`stats_<field>(l)` = `Znth k
   l 0`, declared Extern Coq in solver_qcp_def.h and DEFINED in
   solver_qcp_model.v:1309-1329, which solver_qcp_lib.v re-exports), never by
   position.  Accessor -> `s->stats` field -> index:
     stats_starts       0    stats_conflicts         4    stats_learnts_literals  8
     stats_decisions    1    stats_clauses           5    stats_max_literals      9
     stats_propagations 2    stats_clauses_literals  6    stats_tot_literals     10
     stats_inspects     3    stats_learnts           7
   (see the `store(&(s->stats....), Znth(k, ...))` block in `solver_solve`
   for the site this table is transcribed from).

   CONVENTIONS.  A `which implies` clause is a PARTIAL cut: it matches its LHS
   atoms against the current state, frames everything else untouched, and
   introduces only the RHS's own existentials.  An `Assert` is a FULL cut: it
   restates the entire state reaching that point, so anything not repeated is
   lost and must be re-derived.  A `$ tag` line groups the annotations either
   side of it under one informal branch name for a `Branch name`/`Branch join`
   pair (e.g. `Branch name learnt`), not a separate directive of its own.  A
   trailing `&& emp` on a pure conjunction owns no heap.  `&x` inside
   `has_permission` is the write-permission token for the current binding of
   local `x`; `&#x` is the same token for an outer binding of `x` that a
   narrower scope has shadowed (e.g. `has_permission(&#v)` occurs
   immediately beside `has_permission(&v)` where an inner loop shadows an
   outer `v`) -- both must be threaded separately until the shadow ends.

   TRUSTED BOUNDARY.  Annotations in this file, solver_qcp.h and solver_qcp_def.h
   are checked against solver_qcp_lib.v's specifications.  The exceptions live in
   minisat_qcp_compat.h and are audited, not proved: the native allocator's
   pointer alignment (assumed even, so a clause pointer's low tag bit is
   reliable -- see the comment above `minisat_clause_alloc`), `realloc`'s
   behavior on growth (assumed to preserve the live prefix and leave the new
   tail uninitialised -- see the note above `minisat_int_array_grow`), the
   RNG bodies (requiring and preserving an integer seed in 1..2147483646,
   represented exactly as `Z_to_fp64(z)`, and `size >= 1` for `irand`;
   outputs are range-bounded, with no sequence/distribution guarantee), and
   budget casts: `minisat_budget_to_int` has an unconstrained verification result;
   `minisat_uint64_sum_to_int` specifies addition modulo 2^64 followed by
   signed low-32-bit narrowing.  Restart/reduce scheduling is heuristic and
   cannot by itself justify a SAT or UNSAT verdict.
   =========================================================================== */

#include "solver_qcp.h"
#include "solver_qcp_def.h"

/*@ include strategies "solver_qcp.strategies" */

/* The body behind `assert()': minisat_qcp_compat.h redirects `assert(expr)'
   to this call and declares its contract, which requires the expression to be
   non-zero on entry.  The body is empty because every call site discharges
   that requirement in the proof. */
void qcp_assert(int expr)
{
}

//=================================================================================================
// Debug:

//#define VERBOSEDEBUG

// For derivation output (verbosity level 2)
#define L_IND    "%-*d"
#define L_ind    solver_dlevel(s)*3+3,solver_dlevel(s)
#define L_LIT    "%sx%d"
#define L_lit(p) lit_sign(p)?"~":"", (lit_var(p))

/* Runtime check that stays live in the release build, unlike `assert()`.
   The contract requires the expression to be non-zero on entry and promises
   nothing more: every call site discharges that requirement in the proof, so a
   failing check is unreachable. */
static inline void check(int expr)
/*@ Require expr != 0 && emp
    Ensure emp
 */
{
    assert(expr);
}

/* Decrement the simplification-database propagation budget by one, saturating
   at the smallest int.  Returns the input unchanged there and `value - 1`
   everywhere else, so the counter can never overflow. */
static inline int minisat_simpdb_props_after_propagation(int value)
/*@ Require emp
    Ensure ((value == INT_MIN && __return == value) ||
            (value != INT_MIN && __return == value - 1)) && emp
 */
{
    if (value == (-2147483647 - 1))
        return value;
    return value - 1;
}

/* Test a conflict counter against a budget.  Requires a non-negative count and
   returns 1 exactly when the limit is non-negative and the count has reached
   it, 0 when the limit is negative (no budget) or the count is still below it. */
static inline int minisat_conflict_limit_reached(uint64 count, int limit)
/*@ Require 0 <= count && emp
    Ensure ((__return == 1 && limit >= 0 && count >= limit) ||
            (__return == 0 && (limit < 0 || count < limit))) && emp
 */
{
    return limit >= 0 && count >= (uint64)limit;
}

#ifdef MINISAT_QCP_ENABLE_OUTPUT
/* Print the literals of the range [begin, endvar) in the derivation-output
   format, one space apart, a leading `~' marking a negated literal. */
static void printlits(lit* begin, lit* endvar)
{
    int i;
    for (i = 0; i < endvar - begin; i++)
        printf(L_LIT" ",L_lit(begin[i]));
}
#endif

//=================================================================================================
// Random numbers:


// Returns 0 <= x < 1; seed is an exact integer in 1..2147483646 before and after.
// The double-to-int conversions below are inexpressible in the canonical QCP
// expression language (no fp64-to-Z operation), so the canonical build uses
// the audited external contracts declared in minisat_qcp_compat.h and these
// frozen bodies are native-only.
#ifdef MINISAT_QCP_NATIVE_RUNTIME
static inline double drand(double* seed) {
    int q;
    *seed *= 1389796;
    q = (int)(*seed / 2147483647);
    *seed -= (double)q * 2147483647;
    return *seed / 2147483647; }


// Returns 0 <= x < size; size >= 1 and the same integer-seed domain is required.
static inline int irand(double* seed, int size) {
    return (int)(drand(seed) * size); }
#endif


//=================================================================================================
// Predeclarations:

/* Sort the `size' clause pointers of `array' in place under `clause_cmp'
   (defined below).  The specification promises only a
   permutation of the input of the same length, not the order. */
void sort(void** array, int size)
/*@ sort_spec
    With (db : dbmap) (origin : list Z)
    Require 0 <= size && size <= INT_MAX && Zlength(origin) == size &&
            learnt_sort_domain(db, origin) && NoDup(db_words(db)) &&
            PtrArray::seg(array, 0, size, origin) * clause_db_rep(db)
    Ensure exists (current : list Z),
           Permutation(origin, current) && Zlength(current) == size &&
           PtrArray::seg(array, 0, size, current) * clause_db_rep(db)
 */;

//=================================================================================================
// Clause datatype + minor functions:

struct clause_t
{
    int size_learnt;
    float activity;
    lit lits[0];
};

/* Number of literals in a clause.  The size and the learnt flag share one
   header word; the contract requires that word to be non-negative, returns its
   upper half, and leaves the header untouched. */
static inline int   clause_size       (clause* c)
/*@ With header
    Require 0 <= header && store(clause_hdr_addr(c), int, header)
    Ensure __return == header / 2 &&
           store(clause_hdr_addr(c), int, header)
 */
{ /*@ store(clause_hdr_addr(c), int, header)
       which implies store(&(c->size_learnt), int, header)
   */
  return c->size_learnt >> 1; }

/* Address of a clause's literal array.  Promises exactly the address the
   separation-logic clause representation uses, and reads no memory. */
static inline lit*  clause_begin      (clause* c)
/*@ Require emp
    Ensure __return == clause_lits_addr(c) && emp
 */
{ /*@ Assert c == c@pre && c->lits == clause_lits_addr(c) && emp */
  return c->lits; }

/* Whether a clause is learnt rather than an input clause.  Returns the low bit
   of the shared header word, which the contract requires to be non-negative,
   and leaves the header unchanged. */
static inline int   clause_learnt     (clause* c)
/*@ With header
    Require 0 <= header && store(clause_hdr_addr(c), int, header)
    Ensure __return == header % 2 &&
           store(clause_hdr_addr(c), int, header)
 */
{ /*@ store(clause_hdr_addr(c), int, header)
       which implies store(&(c->size_learnt), int, header)
   */
  return c->size_learnt & 1; }

/* Read an initialized activity cell and return the stored value.  The caller's
   database or sorting invariant supplies any numeric-domain requirement. */
static inline float clause_activity   (clause* c)
/*@ With a
    Require store(clause_act_addr(c), float, a)
    Ensure msat_fp32_same(__return, a) &&
           store(clause_act_addr(c), float, a)
 */
{ /*@ store(clause_act_addr(c), float, a)
       which implies store(&(c->activity), float, a)
   */
  return c->activity; }

/* Overwrite an owned activity cell with the supplied value.  Callers establish
   the numeric-domain facts needed to rebuild their database invariants. */
static inline void  clause_setactivity(clause* c, float a)
/*@ With old
    Require store(clause_act_addr(c), float, old)
    Ensure store(clause_act_addr(c), float, a)
 */
{ /*@ store(clause_act_addr(c), float, old)
       which implies store(&(c->activity), float, old)
   */
  c->activity = a; }

//=================================================================================================
// Encode literals in clause pointers:

/* Encode a literal as a tagged clause pointer.  A binary reason is stored in
   the reason array without allocating a clause: the literal is doubled and the
   low bit set.  Requires a non-negative literal that fits in an int. */
clause* clause_from_lit (lit l)
/*@ Require 0 <= l && l <= INT_MAX && emp
    Ensure __return == tag_of_lit(l) && emp
 */
{ return (clause*)((unsigned long)l + (unsigned long)l + 1);  }

/* Whether a clause pointer is really a tagged literal rather than a heap
   clause.  Returns the low tag bit, and the contract ties each of the two
   results to the tag predicate the proof case-splits on. */
bool    clause_is_lit   (clause* c)
/*@ Require 0 <= c && emp
    Ensure clause_is_lit_result(c, __return) &&
           ((__return == 1 && is_tag(c) == msat_true) ||
            (__return == 0 && is_tag(c) == msat_false)) && emp
 */
{ return ((unsigned long)c & 1);                              }

/* Decode the literal carried by a tagged clause pointer.  Requires the word to
   be tagged and its literal to fit in an int, and returns that literal. */
lit     clause_read_lit (clause* c)
/*@ Require 0 <= c && tagged_word(c) &&
            0 <= tag_lit(c) && tag_lit(c) <= INT_MAX && emp
    Ensure __return == tag_lit(c) && emp
 */
{ return (lit)((unsigned long)c >> 1);                        }

//=================================================================================================
// Simple helpers:

/* Current decision level: the number of levels recorded in the trail-limit
   vector.  Returns 0 on an empty vector and leaves the vector unchanged. */
static inline int     solver_dlevel(solver* s)
/*@ With (lim : list Z) lim_cap
    Require veci_rep(&(s->trail_lim), lim, lim_cap)
    Ensure __return == Zlength(lim) &&
           (lim == z_nil => __return == 0) &&
           veci_rep(&(s->trail_lim), lim, lim_cap)
 */
{ return veci_size(&s->trail_lim); }

/* Address of the watcher-list slot for a nonnegative literal index.
   Leaves the owned array handle intact; accessing the slot contents still
   requires the caller to establish the corresponding array footprint. */
static inline vecp*   solver_read_wlist     (solver* s, lit l)
/*@ With rdw_wl
    Require 0 <= l && solver_wlists_handle(s, rdw_wl)
    Ensure __return == vecp_slot(rdw_wl, l) && solver_wlists_handle(s, rdw_wl)
 */
{ /*@ solver_wlists_handle(s, rdw_wl)
       which implies store(&(s->wlists), vecp *, rdw_wl)
   */
  return &s->wlists[l]; }

/* Remove the first occurrence of `e` from a watcher list, shifting the later
   entries down one slot and shrinking the vector.  Requires `e` actually to
   occur in the focused list; the postcondition rebuilds the whole watcher
   structure with just that one list replaced. */
static inline void    vecp_remove(vecp* v, void* e)
/*@ With base vr_n index (wm : list (list Z)) (caps : list Z)
    Require 0 <= index && index < 2 * vr_n &&
            Zlength(wm) == 2 * vr_n && Zlength(caps) == 2 * vr_n &&
            vecp_remove_member(e, Znth(index, wm, nil)) &&
            wlists_focus_at(base, index, wm, caps, v)
    Ensure exists found,
             vecp_remove_found(e, Znth(index, wm, nil), found) &&
             wlists_rep(base, vr_n,
               replace_Znth(index,
                 vecp_remove_result(Znth(index, wm, nil), found), wm),
               caps)
 */
{
    /*@ wlists_focus_at(base, index, wm, caps, v)
        which implies
        exists p (pre post : list (list Z)) (words0 : list Z)
                 (capspre capspost : list Z) cap,
          wm == app(pre, cons(words0, post)) &&
          caps == app(capspre, cons(cap, capspost)) &&
          Zlength(pre) == index && Zlength(capspre) == index &&
          v == vecp_slot(base, index) &&
          0 <= Zlength(words0) && Zlength(words0) <= cap &&
          0 < cap && cap <= INT_MAX &&
          store(&(v->size), int, Zlength(words0)) *
          store(&(v->cap), int, cap) *
          store(&(v->ptr), void **, p) *
          PtrArray::seg(p, 0, Zlength(words0), words0) *
          PtrArray::undef_seg(p, Zlength(words0), cap) *
          wlists_rep_from(base, 0, pre, capspre) *
          wlists_rep_from(base, index + 1, post, capspost)
     */
    /*@ Given p pre post words0 capspre capspost cap */
    void** ws = vecp_begin(v);
    int    j  = 0;

    /* Both loop cuts restate the six `wm`/`caps`/`pre`/`capspre` facts.
       `Inv Assert` is a FULL cut: a pure fact that is not restated is
       DESTROYED, and the final `which implies` before the exit `Assert`
       opens with exactly these six conjuncts.  Nothing in either loop
       touches wm, caps, pre, post, capspre, capspost, index or vr_n. */
    /*@ Inv Assert e == e@pre &&
                   vecp_remove_scan_inv(e, words0, j) &&
                   wm == app(pre, cons(words0, post)) &&
                   caps == app(capspre, cons(cap, capspost)) &&
                   Zlength(pre) == index && Zlength(capspre) == index &&
                   Zlength(wm) == 2 * vr_n && Zlength(caps) == 2 * vr_n &&
                   v == vecp_slot(base, index) &&
                   0 <= j && j < Zlength(words0) &&
                   0 <= Zlength(words0) && Zlength(words0) <= cap &&
                   0 < cap && cap <= INT_MAX &&
                   store(&(v->size), int, Zlength(words0)) *
                   store(&(v->cap), int, cap) *
                   store(&(v->ptr), void **, ws) *
                   PtrArray::seg(ws, 0, Zlength(words0), words0) *
                   PtrArray::undef_seg(ws, Zlength(words0), cap) *
                   wlists_rep_from(base, 0, pre, capspre) *
                   wlists_rep_from(base, index + 1, post, capspost)
     */
    for (; ws[j] != e  ; j++);
    assert(j < vecp_size(v));
    /*@ Inv Assert exists found (words_now : list Z),
                   e == e@pre &&
                   vecp_remove_shift_inv(e, words0, found, j, words_now) &&
                   wm == app(pre, cons(words0, post)) &&
                   caps == app(capspre, cons(cap, capspost)) &&
                   Zlength(pre) == index && Zlength(capspre) == index &&
                   Zlength(wm) == 2 * vr_n && Zlength(caps) == 2 * vr_n &&
                   v == vecp_slot(base, index) &&
                   0 <= j && j < Zlength(words_now) &&
                   0 <= Zlength(words_now) && Zlength(words_now) <= cap &&
                   0 < cap && cap <= INT_MAX &&
                   store(&(v->size), int, Zlength(words_now)) *
                   store(&(v->cap), int, cap) *
                   store(&(v->ptr), void **, ws) *
                   PtrArray::seg(ws, 0, Zlength(words_now), words_now) *
                   PtrArray::undef_seg(ws, Zlength(words_now), cap) *
                   wlists_rep_from(base, 0, pre, capspre) *
                   wlists_rep_from(base, index + 1, post, capspost)
     */
    for (; j < vecp_size(v)-1; j++) ws[j] = ws[j+1];
    /*@ Given found words_now */
    /*@ vecp_remove_shift_inv(
          e, words0, found, j, words_now) &&
          j >= Zlength(words_now) - 1 &&
          j < Zlength(words_now)
        which implies
          vecp_remove_found(e, words0, found) &&
          1 <= Zlength(words_now) &&
          sublist(0, Zlength(words_now) - 1, words_now) ==
            vecp_remove_result(words0, found) &&
          has_permission(&j)
     */
    vecp_resize(v,vecp_size(v)-1);
    /*@ wm == app(pre, cons(words0, post)) &&
          caps == app(capspre, cons(cap, capspost)) &&
          Zlength(pre) == index &&
          Zlength(capspre) == index &&
          v == vecp_slot(base, index) &&
          Zlength(wm) == 2 * vr_n && Zlength(caps) == 2 * vr_n &&
          sublist(0, Zlength(words_now) - 1, words_now) ==
            vecp_remove_result(words0, found) &&
          vecp_rep(
            v, sublist(0, Zlength(words_now) - 1, words_now), cap) *
          wlists_rep_from(base, 0, pre, capspre) *
          wlists_rep_from(base, index + 1, post, capspost)
        which implies
          wlists_rep(
            base, vr_n,
            replace_Znth(index,
              vecp_remove_result(words0, found), wm),
            caps) *
          has_permission(&v)
     */
}

//=================================================================================================
// Variable order functions:

/* Repair the variable-order heap after variable `v`'s activity rose: sift `v`
   up until its parent's activity is at least its own.  Requires `v` to be in
   the heap, and promises a heap that still satisfies the order invariant and
   holds the same variables. */
static inline void order_update(solver* s, int v) // updateorder
/*@ With n (heap0 orderpos0 : list Z) (activity0 : list fp64)
          order_cap orderpos_ptr activity_ptr
    Require order_update_pre(n, v, heap0, orderpos0) &&
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos0) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            veci_rep(&(s->order), heap0, order_cap)
    Ensure exists heap1 orderpos1,
            order_update_post(n, v, heap0, orderpos0, heap1, orderpos1) &&
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos1) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            veci_rep(&(s->order), heap1, order_cap)
 */
{
    /*@ order_update_pre(n, v, heap0, orderpos0)
        which implies
          order_update_pre(n, v, heap0, orderpos0) &&
          0 <= v && v < n &&
          0 <= Znth(v, orderpos0, -1) &&
          Znth(v, orderpos0, -1) < Zlength(heap0) &&
          0 <= Znth(Znth(v, orderpos0, -1), heap0, 0) &&
          Znth(Znth(v, orderpos0, -1), heap0, 0) < n
     */
    /*@ veci_rep(&(s->order), heap0, order_cap)
        which implies exists order_ptr,
          0 <= Zlength(heap0) && Zlength(heap0) <= order_cap &&
          0 < order_cap && order_cap <= INT_MAX &&
          store(&(s->order.size), int, Zlength(heap0)) *
          store(&(s->order.cap), int, order_cap) *
          store(&(s->order.ptr), int *, order_ptr) *
          IntArray::seg(order_ptr, 0, Zlength(heap0), heap0) *
          IntArray::undef_seg(order_ptr, Zlength(heap0), order_cap)
     */
    /*@ Given order_ptr */
    int*    orderpos = s->orderpos;
    double* activity = s->activity;
    int*    heap     = veci_begin(&s->order);
    int     i        = orderpos[v];
    /*@ 0 <= i && i < Zlength(heap0) by local */
    int     x        = heap[i];
    /*@ 0 <= x && x < n by local */
    int     parent   = (i - 1) / 2;

    assert(s->orderpos[v] != -1);

    /*@ Inv Assert exists heap_now orderpos_now,
                   s == s@pre && v == v@pre &&
                   order_update_pre(n, v, heap0, orderpos0) &&
                   Zlength(activity0) == n &&
                   order_update_loop_inv(n, v, heap0, x, i,
                                         heap_now, orderpos_now) &&
                   orderpos == orderpos_ptr &&
                   activity == activity_ptr && heap == order_ptr &&
                   0 <= x && x < n &&
                   0 <= i && i < Zlength(heap_now) &&
                   parent == (i - 1) / 2 &&
                   0 <= parent && parent < Zlength(heap_now) &&
                   0 <= heap_now[parent - 0] &&
                   heap_now[parent - 0] < n &&
                   store(&(s->orderpos), int *, orderpos_ptr) *
                   store(&(s->activity), double *, activity_ptr) *
                   IntArray::seg(orderpos, 0, n, orderpos_now) *
                   store(&(s->order.size), int, Zlength(heap_now)) *
                   store(&(s->order.cap), int, order_cap) *
                   store(&(s->order.ptr), int *, heap) *
                   IntArray::seg(heap, 0, Zlength(heap_now), heap_now) *
                   IntArray::undef_seg(heap, Zlength(heap_now), order_cap) *
                   ((i == 0 &&
                    DoubleArray::seg(activity, 0, n, activity0)) ||
                    (i != 0 &&
                     x != heap_now[parent - 0] &&
                     store(activity + x * sizeof(double), double,
                           double_Znth(x - 0, activity0)) *
                     store(activity +
                             heap_now[parent - 0] * sizeof(double),
                           double,
                           double_Znth(
                             heap_now[parent - 0] - 0, activity0)) *
                     double_array_missing2(
                       activity, x, heap_now[parent - 0], n, activity0)))
     */
    while (i != 0 && activity[x] > activity[heap[parent]]){
        /*@ Given heap_now orderpos_now */
        heap[i]           = heap[parent];
        /*@ 0 <= replace_Znth(i, heap_now[parent - 0], heap_now)[i] &&
            replace_Znth(i, heap_now[parent - 0], heap_now)[i] < n
            by local
         */
        orderpos[heap[i]] = i;
        i                 = parent;
        parent            = (i - 1) / 2;
    }
    heap[i]     = x;
    orderpos[x] = i;
}

/* Hook run when a variable becomes assigned.  This solver leaves assigned
   variables in the order heap and discards them lazily at selection time, so
   the body is empty and the contract touches no state. */
static inline void order_assigned(solver* s, int v)
/*@ Require emp
    Ensure emp
 */
{
}

/* Hook run when variable `v` is unassigned during backtracking: put `v` back
   into the order heap if it is not already there, and sift it into place.
   Promises a heap that still satisfies the order invariant, possibly with a
   larger capacity. */
static inline void order_unassigned(solver* s, int v) // undoorder
/*@ With n (heap0 orderpos0 : list Z) (activity0 : list fp64)
          order_cap orderpos_ptr activity_ptr
    Require order_unassigned_pre(n, v, order_cap, heap0, orderpos0) &&
            Zlength(activity0) == n &&
            store(&(s->size), int, n) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos0) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            veci_rep(&(s->order), heap0, order_cap)
    Ensure exists heap1 orderpos1 order_cap1,
            order_unassigned_post(n, v, order_cap, heap0, orderpos0,
                                  order_cap1, heap1, orderpos1) &&
            store(&(s->size), int, n) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos1) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            veci_rep(&(s->order), heap1, order_cap1)
 */
{
    /*@ order_unassigned_pre(n, v, order_cap, heap0, orderpos0)
        which implies
          order_unassigned_pre(n, v, order_cap, heap0, orderpos0) &&
          0 <= v && v < n && Zlength(heap0) <= order_cap &&
          2 * n <= INT_MAX &&
          (orderpos0[v - 0] != -1 || Zlength(heap0) < n)
     */
    /*@ veci_rep(&(s->order), heap0, order_cap)
        which implies exists order_ptr,
          0 <= Zlength(heap0) && Zlength(heap0) <= order_cap &&
          0 < order_cap && order_cap <= INT_MAX &&
          store(&(s->order.size), int, Zlength(heap0)) *
          store(&(s->order.cap), int, order_cap) *
          store(&(s->order.ptr), int *, order_ptr) *
          IntArray::seg(order_ptr, 0, Zlength(heap0), heap0) *
          IntArray::undef_seg(order_ptr, Zlength(heap0), order_cap)
     */
    int* orderpos = s->orderpos;
    if (orderpos[v] == -1){
        orderpos[v] = veci_size(&s->order);
        check(veci_push(&s->order,v) == 1);
        /*@ IntArray::full(
              orderpos, n,
              replace_Znth(v, Zlength(heap0), orderpos0))
            which implies
            IntArray::seg(
              orderpos, 0, n,
              replace_Znth(v, Zlength(heap0), orderpos0))
         */
        /*@ order_unassigned_pre(
              n, v, order_cap, heap0, orderpos0) &&
            orderpos0[v] == -1
            which implies
            order_update_pre(
              n, v, app(heap0, cons(v, nil)),
              replace_Znth(v, Zlength(heap0), orderpos0))
         */
        order_update(s,v);
    }
}

/* Choose the next decision variable.  With probability `random_var_freq` it
   returns a random variable when that one is unassigned; otherwise it pops the
   highest-activity variable off the order heap, skipping the assigned ones.
   Returns -1 when no unassigned variable is left, and advances the seed. */
static int order_select(solver* s, double random_var_freq) // selectvar
/*@ With n (heap0 orderpos0 assigns0 trail0 : list Z)
          (activity0 : list fp64) qhead order_cap
          orderpos_ptr assigns_ptr activity_ptr seed_value seed_shadow
    Require order_select_pre(n, heap0, orderpos0, assigns0, trail0, qhead) &&
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
            veci_rep(&(s->order), heap0, order_cap)
    Ensure exists heap1 orderpos1 seed_value1 seed_shadow1,
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
            veci_rep(&(s->order), heap1, order_cap)
 */
{
    /*@ order_select_pre(n, heap0, orderpos0, assigns0, trail0, qhead)
        which implies
          order_select_pre(n, heap0, orderpos0, assigns0, trail0, qhead) &&
          0 <= n && Zlength(assigns0) == n
     */
    /*@ veci_rep(&(s->order), heap0, order_cap)
        which implies exists order_ptr,
          0 <= Zlength(heap0) && Zlength(heap0) <= order_cap &&
          0 < order_cap && order_cap <= INT_MAX &&
          store(&(s->order.size), int, Zlength(heap0)) *
          store(&(s->order.cap), int, order_cap) *
          store(&(s->order.ptr), int *, order_ptr) *
          IntArray::seg(order_ptr, 0, Zlength(heap0), heap0) *
          IntArray::undef_seg(order_ptr, Zlength(heap0), order_cap)
     */
    /*@ Given order_ptr */
    int*    heap;
    double* activity;
    int*    orderpos;

    lbool* values = s->assigns;

    // Random decision:
    if (s->size > 0 &&
        drand(&s->random_seed)
          /*@ where z = seed_shadow @mark order_select_drand */ < random_var_freq){
        /*@ Given seed_shadow_after_drand from z2 of order_select_drand */
        int next = irand(&s->random_seed,s->size)
          /*@ where z = seed_shadow_after_drand */;
        assert(next >= 0 && next < s->size);
        /*@ 0 <= next && next < n by local */
        if (values[next] == MINISAT_QCP_ZERO_VALUE)
            return next;
    }

    // Activity based decision:

    heap     = veci_begin(&s->order);
    activity = s->activity;
    orderpos = s->orderpos;


    /*@ Inv Assert exists heap_now orderpos_now seed_value_now seed_shadow_now,
                   s == s@pre &&
                   order_select_loop_inv(n, heap0, heap_now, orderpos_now,
                                         assigns0, trail0, qhead) &&
                   heap == order_ptr && activity == activity_ptr &&
                   orderpos == orderpos_ptr && values == assigns_ptr &&
                   seed_value_now == Z_to_fp64(seed_shadow_now) &&
                   1 <= seed_shadow_now && seed_shadow_now <= 2147483646 &&
                   store(&(s->size), int, n) *
                   store(&(s->random_seed), double, seed_value_now) *
                   store(&(s->orderpos), int *, orderpos_ptr) *
                   store(&(s->assigns), char *, assigns_ptr) *
                   store(&(s->activity), double *, activity_ptr) *
                   IntArray::seg(orderpos, 0, n, orderpos_now) *
                   CharArray::seg(values, 0, n, assigns0) *
                   DoubleArray::seg(activity, 0, n, activity0) *
                   veci_rep_at(&(s->order), heap, heap_now, order_cap) *
                   has_permission(&random_var_freq)
     */
    while (veci_size(&s->order) > 0){
        /*@ Given heap_now orderpos_now seed_value_now seed_shadow_now */
        /*@ 0 < Zlength(heap_now) by local */
        /*@ 0 <= Znth(0, heap_now, 0) && Znth(0, heap_now, 0) < n by local */
        int    next  = heap[0];
        /*@ 0 <= next && next < n by local */
        int    size  = veci_size(&s->order)-1;
        /*@ 0 <= size && size < Zlength(heap_now) by local */
        /*@ 0 <= Znth(size, heap_now, 0) && Znth(size, heap_now, 0) < n by local */
        int    x     = heap[size];
        /*@ 0 <= x && x < n by local */

        veci_resize(&s->order,size);

        orderpos[next] = -1;

        if (size > 0){
            double act   = activity[x];

            int    i     = 0;
            int    child = 1;


            /*@ Inv Assert exists sift_heap_before sift_heap_now
                                 sift_orderpos_now
                                 sift_seed_value_now sift_seed_shadow_now,
                           s == s@pre &&
                           order_select_sift_inv(n, next, x, i,
                             heap0, sift_heap_before, sift_heap_now,
                             sift_orderpos_now,
                             assigns0, trail0, qhead) &&
                           Zlength(activity0) == n &&
                           heap == order_ptr &&
                           activity == activity_ptr &&
                           orderpos == orderpos_ptr &&
                           values == assigns_ptr &&
                           sift_seed_value_now ==
                             Z_to_fp64(sift_seed_shadow_now) &&
                           1 <= sift_seed_shadow_now &&
                           sift_seed_shadow_now <= 2147483646 &&
                           0 < n && 0 <= next && next < n &&
                           0 <= x && x < n &&
                           Zlength(sift_heap_now) == size &&
                           0 <= i && i < Zlength(sift_heap_now) &&
                           1 <= child &&
                           child == 2 * i + 1 &&
                           store(&(s->size), int, n) *
                           store(&(s->random_seed), double,
                                 sift_seed_value_now) *
                           store(&(s->orderpos), int *, orderpos_ptr) *
                           store(&(s->assigns), char *, assigns_ptr) *
                           store(&(s->activity), double *, activity_ptr) *
                           IntArray::seg(
                             orderpos, 0, n, sift_orderpos_now) *
                           CharArray::seg(values, 0, n, assigns0) *
                           store(&(s->order.size), int,
                                 Zlength(sift_heap_now)) *
                           store(&(s->order.cap), int, order_cap) *
                           store(&(s->order.ptr), int *, heap) *
                           IntArray::seg(
                             heap, 0, Zlength(sift_heap_now),
                             sift_heap_now) *
                           IntArray::undef_seg(
                             heap, Zlength(sift_heap_now), order_cap) *
                           has_permission(&random_var_freq) *
                           store(&act, double,
                                 double_Znth(x - 0, activity0)) *
                           ((size <= child &&
                             DoubleArray::seg(
                               activity, 0, n, activity0)) ||
                            (child < size && size <= child + 1 &&
                             0 <= sift_heap_now[child - 0] &&
                             sift_heap_now[child - 0] < n &&
                             store(activity +
                                     sift_heap_now[child - 0] *
                                       sizeof(double),
                                   double,
                                   double_Znth(
                                     sift_heap_now[child - 0] - 0,
                                     activity0)) *
                             DoubleArray::missing_i(
                               activity, sift_heap_now[child - 0],
                               0, n, activity0)) ||
                            (child + 1 < size &&
                             0 <= sift_heap_now[child - 0] &&
                             sift_heap_now[child - 0] < n &&
                             0 <= sift_heap_now[child + 1 - 0] &&
                             sift_heap_now[child + 1 - 0] < n &&
                             sift_heap_now[child - 0] !=
                               sift_heap_now[child + 1 - 0] &&
                             store(activity +
                                     sift_heap_now[child - 0] *
                                       sizeof(double),
                                   double,
                                   double_Znth(
                                     sift_heap_now[child - 0] - 0,
                                     activity0)) *
                             store(activity +
                                     sift_heap_now[child + 1 - 0] *
                                       sizeof(double),
                                   double,
                                   double_Znth(
                                     sift_heap_now[child + 1 - 0] - 0,
                                     activity0)) *
                             double_array_missing2(
                               activity, sift_heap_now[child - 0],
                               sift_heap_now[child + 1 - 0], n,
                               activity0)))
             */
            while (child < size){
                /*@ Given sift_heap_before sift_heap_now
                            sift_orderpos_now
                            sift_seed_value_now sift_seed_shadow_now */
                if (child+1 < size && activity[heap[child]] < activity[heap[child+1]])
                    child++;

                assert(child < size);

                if (act >= activity[heap[child]])
                    break;

                heap[i]           = heap[child];
                /*@ 0 <= replace_Znth(
                          i, sift_heap_now[child - 0],
                          sift_heap_now)[i] &&
                    replace_Znth(
                      i, sift_heap_now[child - 0],
                      sift_heap_now)[i] < n
                    by local
                 */
                orderpos[heap[i]] = i;
                i                 = child;
                child             = 2 * child + 1;
            }
            /*@ Given sift_heap_before sift_heap_now
                        sift_orderpos_now
                        sift_seed_value_now sift_seed_shadow_now */
            heap[i]           = x;
            /*@ 0 <= replace_Znth(i, x, sift_heap_now)[i] &&
                replace_Znth(i, x, sift_heap_now)[i] < n
                by local
             */
            orderpos[heap[i]] = i;
        }

        if (values[next] == MINISAT_QCP_ZERO_VALUE)
            return next;
    }

    return -MINISAT_QCP_NEGATIVE_ONE_MAGNITUDE;
}

//=================================================================================================
// Activity functions:

/* Rescale every variable activity, and the activity increment, by the same
   tiny factor, so that no activity overflows.  The contract preserves the
   shape and the length of the activity array; the values themselves are left
   unconstrained. */
static inline void act_var_rescale(solver* s)
/*@ With n activity_ptr (activity0 : list fp64) var_inc0
    Require 0 <= n && n <= INT_MAX && Zlength(activity0) == n &&
            store(&(s->size), int, n) *
            store(&(s->activity), double *, activity_ptr) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            store(&(s->var_inc), double, var_inc0)
    Ensure exists (activity1 : list fp64) var_inc1,
            Zlength(activity1) == n &&
            store(&(s->size), int, n) *
            store(&(s->activity), double *, activity_ptr) *
            DoubleArray::seg(activity_ptr, 0, n, activity1) *
            store(&(s->var_inc), double, var_inc1)
 */
{
    double* activity = s->activity;
    int i;
    /*@ Inv Assert exists (activity_now : list fp64),
                   s == s@pre &&
                   0 <= i && i <= n && Zlength(activity_now) == n &&
                   activity == activity_ptr &&
                   store(&(s->size), int, n) *
                   store(&(s->activity), double *, activity_ptr) *
                   store(&(s->var_inc), double, var_inc0) *
                   ((i == n &&
                    DoubleArray::seg(
                       activity, 0, n, activity_now)) ||
                    (i < n &&
                     store(activity + i * sizeof(double), double,
                           double_Znth(i - 0, activity_now)) *
                     DoubleArray::missing_i(
                       activity, i, 0, n, activity_now)))
     */
    for (i = 0; i < s->size; i++)
        activity[i] *= 1e-100;
    s->var_inc *= 1e-100;
}

/* Bump variable `v`'s activity by the current increment, rescaling everything
   if it grows too large, then repair the order heap.  Promises a heap that is
   a permutation of the old one, still well formed, and holding exactly the
   same variables as before. */
static inline void act_var_bump(solver* s, int v)
/*@ With n (heap0 orderpos0 : list Z) (activity0 : list fp64)
          order_cap orderpos_ptr activity_ptr var_inc0
    Require order_heap_wf(n, heap0, orderpos0) && 0 <= v && v < n &&
            Zlength(activity0) == n &&
            store(&(s->size), int, n) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos0) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            veci_rep(&(s->order), heap0, order_cap) *
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
            veci_rep(&(s->order), heap1, order_cap) *
            store(&(s->var_inc), double, var_inc1)
 */
{
    double* activity = s->activity;
    activity[v] += s->var_inc;
    if (activity[v] > 1e100)
        act_var_rescale(s);

    /*@ Assert exists (activity1 : list fp64) var_inc_now,
          s == s@pre &&
          order_heap_wf(n, heap0, orderpos0) &&
          0 <= v && v < n && Zlength(activity1) == n &&
          activity == activity_ptr &&
          store(&(s->size), int, n) *
          store(&(s->orderpos), int *, orderpos_ptr) *
          store(&(s->activity), double *, activity_ptr) *
          IntArray::seg(orderpos_ptr, 0, n, orderpos0) *
          DoubleArray::seg(activity_ptr, 0, n, activity1) *
          veci_rep(&(s->order), heap0, order_cap) *
          store(&(s->var_inc), double, var_inc_now)
     */

    //printf("bump %d %f\n", v-1, activity[v]);

    if (s->orderpos[v] != -1)
        order_update(s,v);

}

/* Decay the variable-activity increment by multiplying it by the decay factor,
   so that later bumps count for more than earlier ones.  Only the increment
   cell changes. */
static inline void act_var_decay(solver* s)
/*@ With var_inc0 var_decay0
    Require store(&(s->var_inc), var_inc0) *
            store(&(s->var_decay), var_decay0)
    Ensure exists var_inc1,
           store(&(s->var_inc), var_inc1) *
           store(&(s->var_decay), var_decay0)
 */
{ s->var_inc *= s->var_decay; }

/* Rescale the activity of every learnt clause, and the clause increment, by
   the same tiny factor, so that no clause activity overflows.  The learnt
   database keeps its shape and every activity stays non-negative. */
static inline void act_clause_rescale(solver* s)
/*@ With (db : dbmap) db_cap cla_inc0
    Require learnt_db(db) && msat_fp32_nonnegative(cla_inc0) &&
            vecp_rep(&(s->learnts), db_words(db), db_cap) *
            clause_db_rep(db) *
            store(&(s->cla_inc), cla_inc0)
    Ensure exists cla_inc1,
           msat_fp32_nonnegative(cla_inc1) &&
           vecp_rep(&(s->learnts), db_words(db), db_cap) *
           clause_db_rep(db) *
           store(&(s->cla_inc), cla_inc1)
 */
{
    clause** cs = (clause**)vecp_begin(&s->learnts);
    int i;
    /*@ Inv Assert s == s@pre &&
                   0 <= i && i <= Zlength(db_words(db)) && learnt_db(db) &&
                   msat_fp32_nonnegative(cla_inc0) &&
                   vecp_rep_at(&(s->learnts), cs, db_words(db), db_cap) *
                   clause_db_rep(db) *
                   store(&(s->cla_inc), cla_inc0)
     */
    for (i = 0; i < vecp_size(&s->learnts); i++){
        /*@ learnt_db(db) && 0 <= i && i < Zlength(db_words(db)) &&
              clause_db_rep(db)
            which implies exists (clause_words : list Z)
                                 (activity_now : fp32),
              learnt_db(db) &&
              msat_fp32_nonnegative(activity_now) &&
              0 < db_words(db)[i - 0] &&
              db_words(db)[i - 0] % 2 == 0 &&
              store(clause_hdr_addr(db_words(db)[i - 0]), int,
                    clause_hdr_word(msat_true, Zlength(clause_words))) *
              store(clause_act_addr(db_words(db)[i - 0]), float,
                    activity_now) *
              IntArray::seg(clause_lits_addr(db_words(db)[i - 0]), 0,
                            Zlength(clause_words), clause_words) *
              clause_db_pair_remainder(db_nil, db,
                                       db_words(db)[i - 0], msat_true,
                                       clause_words)
         */
        /*@ Given clause_words activity_now */
        float a = clause_activity(cs[i]);
        clause_setactivity(cs[i], a * 1e-20f);
        /*@ exists (activity_after a_v : fp32),
            learnt_db(db) &&
            msat_fp32_nonnegative(activity_after) &&
            msat_fp32_nonnegative(a_v) &&
            0 < db_words(db)[i - 0] &&
            db_words(db)[i - 0] % 2 == 0 &&
            store(&a, float, a_v) *
            store(clause_hdr_addr(db_words(db)[i - 0]), int,
                  clause_hdr_word(msat_true, Zlength(clause_words))) *
            store(clause_act_addr(db_words(db)[i - 0]), float,
                  activity_after) *
            IntArray::seg(clause_lits_addr(db_words(db)[i - 0]), 0,
                          Zlength(clause_words), clause_words) *
            clause_db_pair_remainder(db_nil, db,
                                     db_words(db)[i - 0], msat_true,
                                     clause_words)
            which implies learnt_db(db) &&
                          0 < db_words(db)[i - 0] &&
                          msat_fp32_nonnegative(a_v) &&
                          store(&a, float, a_v) *
                          clause_db_rep(db)
         */
    }
    s->cla_inc *= 1e-20f;
}


/* Bump learnt clause `c`'s activity by the current clause increment, rescaling
   the whole database if it grows too large.  Requires `c` to be one of the
   learnt clauses; the database keeps its shape and every activity stays
   non-negative. */
static inline void act_clause_bump(solver* s, clause *c)
/*@ With (db : dbmap) db_cap cla_inc0
    Require learnt_db(db) && In(c, db_words(db)) &&
            msat_fp32_nonnegative(cla_inc0) &&
            vecp_rep(&(s->learnts), db_words(db), db_cap) *
            clause_db_rep(db) *
            store(&(s->cla_inc), cla_inc0)
    Ensure exists cla_inc1,
           msat_fp32_nonnegative(cla_inc1) &&
           vecp_rep(&(s->learnts), db_words(db), db_cap) *
           clause_db_rep(db) *
           store(&(s->cla_inc), cla_inc1)
 */
{
    /*@ learnt_db(db) && In(c, db_words(db)) && clause_db_rep(db)
        which implies exists (clause_words : list Z)
                             (activity_now : fp32),
          learnt_db(db) && In(c, db_words(db)) &&
          msat_fp32_nonnegative(activity_now) &&
          0 < c && c % 2 == 0 &&
          store(clause_hdr_addr(c), int,
                clause_hdr_word(msat_true, Zlength(clause_words))) *
          store(clause_act_addr(c), float, activity_now) *
          IntArray::seg(clause_lits_addr(c), 0,
                        Zlength(clause_words), clause_words) *
          clause_db_pair_remainder(db_nil, db, c, msat_true, clause_words)
     */
    /*@ Given clause_words activity_now */
    float a = clause_activity(c) + s->cla_inc;
    clause_setactivity(c,a);
    /*@ exists (a_v : fp32),
        learnt_db(db) && 0 < c && c % 2 == 0 &&
        msat_fp32_nonnegative(a_v) &&
        store(&a, float, a_v) *
        store(clause_hdr_addr(c), int,
              clause_hdr_word(msat_true, Zlength(clause_words))) *
        store(clause_act_addr(c), float, a_v) *
        IntArray::seg(clause_lits_addr(c), 0,
                      Zlength(clause_words), clause_words) *
        clause_db_pair_remainder(db_nil, db, c, msat_true, clause_words)
        which implies learnt_db(db) && In(c, db_words(db)) &&
                      msat_fp32_nonnegative(a_v) &&
                      store(&a, float, a_v) *
                      clause_db_rep(db)
     */
    if (a >= 1e20f) act_clause_rescale(s);
}

/* Decay the clause-activity increment by multiplying it by the clause decay
   factor.  Requires that factor to be positive and finite, and promises the
   increment is still non-negative. */
static inline void act_clause_decay(solver* s)
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
 */
{ s->cla_inc *= s->cla_decay; }


//=================================================================================================
// Clause functions:

/* Allocate a clause over the literals in [begin, endvar), register it in the
   watcher lists of the negations of its first two literals, and append it to
   `database` -- the problem clauses or the learnt clauses, selected by
   `learnt`.  Requires at least two literals with no variable occurring twice.
   Returns 1, or -2 when the allocator or one of the vectors cannot grow. */
static int clause_new(solver *s, lit *begin, lit *endvar, int learnt,
                      vecp *database, clause **clause_out)
/*@ clause_new_spec
    With lvl cn_n (cn_F : cnf) (cn_A_arr cn_A_inst : list literal) (cn_M : msolver)
         (cn_words : list Z)
         (cn_sel : Z) (cn_wl : Z) (cn_root : Z)
    Require learnt == cn_sel && 0 <= cn_sel && cn_sel <= 1 &&
            database == solver_selected_vec(s, cn_sel) &&
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
            IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
            undef_data_at(clause_out, clause *)
    Ensure clause_new_post_at_root(s, begin, clause_out, lvl, cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_words, __return, cn_sel, cn_wl, cn_root)
 */
{
    /*@ learnt == cn_sel && 0 <= cn_sel && cn_sel <= 1 &&
            database == solver_selected_vec(s, cn_sel) &&
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
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
          undef_data_at(clause_out, clause *)
        which implies
          learnt == cn_sel && 0 <= cn_sel && cn_sel <= 1 &&
            database == solver_selected_vec(s, cn_sel) &&
          endvar == begin + Zlength(cn_words) * sizeof(int) &&
          2 <= Zlength(cn_words) &&
          2 * Zlength(cn_words) + 1 <= INT_MAX &&
          cn_n == ms_size(cn_M) && solver_shape(cn_M) &&
          solver_support_inv(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_root, cn_M) &&
          ms_capacity_root_propagation_pending(cn_M) == 0 &&
          msolver_seed_shadow(cn_M) &&
          clause_install_pending_cert(cn_n, cn_F, msolver_set_root(cn_M, cn_root), cn_words, solver_selected_is_learnt(cn_sel)) &&
          vecp_slot(cn_wl, lit_neg_c(cn_words[0 - 0])) !=
            vecp_slot(cn_wl, lit_neg_c(cn_words[1 - 0])) &&
          store(&(s->size), cn_n) *
          solver_wlists_handle(s, cn_wl) *
          vecp_rep(solver_selected_vec(s, cn_sel), db_words(solver_selected_db(cn_sel, cn_M)),
                   solver_selected_cap(cn_sel, cn_M)) *
          wlists_rep(cn_wl, cn_n, ms_wm(cn_M), ms_wcaps(cn_M)) *
          clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
          clause_new_frame_at_gen(s, cn_M, lvl, cn_sel) *
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
          undef_data_at(clause_out, clause *)
     */
    /*@ 0 <= cn_sel && cn_sel <= 1 && endvar == begin + Zlength(cn_words) * sizeof(int) &&
          0 <= Zlength(cn_words) &&
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words)
        which implies
          endvar - begin == Zlength(cn_words) &&
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words)
     */
    int size = (int)(endvar - begin);
    vecp *watch0 = solver_read_wlist(s, lit_neg(begin[0]) /*@ where (original) */);
    vecp *watch1 = solver_read_wlist(s, lit_neg(begin[1]) /*@ where (original) */);
    clause *c;
    int i;

    *clause_out = (clause *)0;
    assert(size > 1);
    assert(learnt >= 0 && learnt < 2);
    /*@ watch0 != watch1 by local */
    assert(watch0 != watch1);

    /* The five semantic conjuncts are restated on the LHS.  Without them this
       block's `which_implies_wit' goal had ZERO hypotheses and still demanded
       `msolver_inv(n, F, A_arr, A_inst, M)': `F', `A_arr' and `A_inst' are
       purely logical, so NO spatial atom can carry them, and the goal was
       refutable by instantiating `A_arr := []'.  All five are ambient here
       (the transaction-entry block above emits them), so the obligation lands
       in a `partial_solve_wit_*_pure' goal that does see the ambient PreH list. */
    /*@ 0 <= cn_sel && cn_sel <= 1 && 2 <= Zlength(cn_words) &&
        2 * Zlength(cn_words) + 1 <= INT_MAX &&
        Forall(lit_wf_c(cn_n), cn_words) &&
        NoDup(map(lit_var_c, cn_words)) &&
        solver_shape(cn_M) &&
          solver_support_inv(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_root, cn_M) &&
        ms_capacity_root_propagation_pending(cn_M) == 0 &&
        msolver_seed_shadow(cn_M) &&
        watch0 == vecp_slot(cn_wl, lit_neg_c(Znth(0, cn_words, 0))) &&
        watch1 == vecp_slot(cn_wl, lit_neg_c(Znth(1, cn_words, 0))) &&
        store(&(s->size), cn_n) *
        solver_wlists_handle(s, cn_wl) *
        vecp_rep(solver_selected_vec(s, cn_sel), db_words(solver_selected_db(cn_sel, cn_M)),
                 solver_selected_cap(cn_sel, cn_M)) *
        wlists_rep(cn_wl, cn_n, ms_wm(cn_M), ms_wcaps(cn_M)) *
        clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
        clause_new_frame_at_gen(s, cn_M, lvl, cn_sel) *
        IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
        store(clause_out, clause *, 0)
        which implies
        exists (watch_words0 watch_words1 : list Z) watch_cap0 watch_cap1,
          2 <= Zlength(cn_words) &&
          2 * Zlength(cn_words) + 1 <= INT_MAX &&
          Forall(lit_wf_c(cn_n), cn_words) &&
          NoDup(map(lit_var_c, cn_words)) &&
          solver_shape(cn_M) &&
          solver_support_inv(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_root, cn_M) &&
          ms_capacity_root_propagation_pending(cn_M) == 0 &&
          msolver_seed_shadow(cn_M) &&
          watch_words0 == Znth(lit_neg_c(Znth(0, cn_words, 0)),
                               ms_wm(cn_M), nil) &&
          watch_words1 == Znth(lit_neg_c(Znth(1, cn_words, 0)),
                               ms_wm(cn_M), nil) &&
          watch_cap0 == Znth(lit_neg_c(Znth(0, cn_words, 0)),
                             ms_wcaps(cn_M), 1) &&
          watch_cap1 == Znth(lit_neg_c(Znth(1, cn_words, 0)),
                             ms_wcaps(cn_M), 1) &&
          vecp_rep(solver_selected_vec(s, cn_sel), db_words(solver_selected_db(cn_sel, cn_M)),
                   solver_selected_cap(cn_sel, cn_M)) *
          vecp_rep(watch0, watch_words0, watch_cap0) *
          vecp_rep(watch1, watch_words1, watch_cap1) *
          clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
          clause_new_transaction_rest_at_gen(s, cn_wl,
            lit_neg_c(Znth(0, cn_words, 0)),
            lit_neg_c(Znth(1, cn_words, 0)), cn_M, lvl, cn_sel) *
          store(&(s->size), cn_n) *
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
          store(clause_out, clause *, 0)
     */
    /*@ Given watch_words0 watch_words1 */

    /*@ Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
          clause_out == clause_out@pre &&
          size == Zlength(cn_words) && learnt == cn_sel &&
          clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_M, cn_words, cn_sel, cn_root) &&
          database == solver_selected_vec(s, cn_sel) &&
          watch0 == vecp_slot(cn_wl, lit_neg_c(Znth(0, cn_words, 0))) &&
          watch1 == vecp_slot(cn_wl, lit_neg_c(Znth(1, cn_words, 0))) &&
          watch_words0 ==
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wm(cn_M), nil) &&
          watch_words1 ==
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wm(cn_M), nil) &&
          lit_neg_c(Znth(0, cn_words, 0)) !=
            lit_neg_c(Znth(1, cn_words, 0)) &&
          vecp_rep(database, db_words(solver_selected_db(cn_sel, cn_M)),
                   solver_selected_cap(cn_sel, cn_M)) *
          vecp_rep(watch0,
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wm(cn_M), nil),
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wcaps(cn_M), 1)) *
          vecp_rep(watch1,
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wm(cn_M), nil),
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wcaps(cn_M), 1)) *
          clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
          clause_new_transaction_rest_at_gen(
            s, cn_wl,
            lit_neg_c(Znth(0, cn_words, 0)),
            lit_neg_c(Znth(1, cn_words, 0)), cn_M, lvl, cn_sel) *
          store(&(s->size), cn_n) *
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
          store(clause_out, clause *, 0) *
          has_permission(&endvar) * has_permission(&c) * has_permission(&i)
     */

    if (vecp_reserve(database) == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        /*@ Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
                   clause_out == clause_out@pre &&
                   clause_new_post_at_root(s, begin, clause_out, lvl, cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_words, -2, cn_sel, cn_wl, cn_root) *
                    has_permission(&endvar) *
                    has_permission(&size) * has_permission(&watch0) *
                    has_permission(&watch1) * has_permission(&c) *
                    has_permission(&i) * has_permission(&learnt) *
                    has_permission(&database) */
        return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    /*@ Assert exists Mstage1 learnt_cap1, 0 <= cn_sel && cn_sel <= 1 &&
          s == s@pre && begin == begin@pre &&
          clause_out == clause_out@pre &&
          size == Zlength(cn_words) && learnt == cn_sel &&
          Mstage1 == msolver_with_clause_caps_gen(
            cn_M, learnt_cap1, ms_wcaps(cn_M), cn_sel) &&
          clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, Mstage1, cn_words, cn_sel, cn_root) &&
          clause_new_reserved_rooms_gen(1, cn_words, Mstage1, cn_sel) &&
          database == solver_selected_vec(s, cn_sel) &&
          watch0 == vecp_slot(cn_wl, lit_neg_c(Znth(0, cn_words, 0))) &&
          watch1 == vecp_slot(cn_wl, lit_neg_c(Znth(1, cn_words, 0))) &&
          watch_words0 ==
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wm(Mstage1), nil) &&
          watch_words1 ==
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wm(Mstage1), nil) &&
          lit_neg_c(Znth(0, cn_words, 0)) !=
            lit_neg_c(Znth(1, cn_words, 0)) &&
          vecp_rep(database, db_words(solver_selected_db(cn_sel, Mstage1)),
                   solver_selected_cap(cn_sel, Mstage1)) *
          vecp_rep(watch0,
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wm(Mstage1), nil),
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wcaps(Mstage1), 1)) *
          vecp_rep(watch1,
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wm(Mstage1), nil),
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wcaps(Mstage1), 1)) *
          clause_db_rep(solver_selected_db(cn_sel, Mstage1)) *
          clause_new_transaction_rest_at_gen(
            s, cn_wl,
            lit_neg_c(Znth(0, cn_words, 0)),
            lit_neg_c(Znth(1, cn_words, 0)), Mstage1, lvl, cn_sel) *
          store(&(s->size), cn_n) *
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
          store(clause_out, clause *, 0) *
          has_permission(&endvar) * has_permission(&c) * has_permission(&i)
     */
    /*@ Given learnt_cap1 */
    if (vecp_reserve(watch0) == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        /*@ Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
                   clause_out == clause_out@pre &&
                   clause_new_post_at_root(s, begin, clause_out, lvl, cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_words, -2, cn_sel, cn_wl, cn_root) *
                    has_permission(&endvar) *
                    has_permission(&size) * has_permission(&watch0) *
                    has_permission(&watch1) * has_permission(&c) *
                    has_permission(&i) * has_permission(&learnt) *
                    has_permission(&database) */
        return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    /*@ Assert exists Mstage2 watch_cap01, 0 <= cn_sel && cn_sel <= 1 &&
          s == s@pre && begin == begin@pre &&
          clause_out == clause_out@pre &&
          size == Zlength(cn_words) && learnt == cn_sel &&
          Mstage2 == msolver_with_clause_caps_gen(
            cn_M, learnt_cap1,
            replace_Znth(
              lit_neg_c(Znth(0, cn_words, 0)), watch_cap01,
              ms_wcaps(cn_M)), cn_sel) &&
          clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, Mstage2, cn_words, cn_sel, cn_root) &&
          clause_new_reserved_rooms_gen(2, cn_words, Mstage2, cn_sel) &&
          database == solver_selected_vec(s, cn_sel) &&
          watch0 == vecp_slot(cn_wl, lit_neg_c(Znth(0, cn_words, 0))) &&
          watch1 == vecp_slot(cn_wl, lit_neg_c(Znth(1, cn_words, 0))) &&
          watch_words0 ==
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wm(Mstage2), nil) &&
          watch_words1 ==
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wm(Mstage2), nil) &&
          lit_neg_c(Znth(0, cn_words, 0)) !=
            lit_neg_c(Znth(1, cn_words, 0)) &&
          vecp_rep(database, db_words(solver_selected_db(cn_sel, Mstage2)),
                   solver_selected_cap(cn_sel, Mstage2)) *
          vecp_rep(watch0,
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wm(Mstage2), nil),
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wcaps(Mstage2), 1)) *
          vecp_rep(watch1,
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wm(Mstage2), nil),
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wcaps(Mstage2), 1)) *
          clause_db_rep(solver_selected_db(cn_sel, Mstage2)) *
          clause_new_transaction_rest_at_gen(
            s, cn_wl,
            lit_neg_c(Znth(0, cn_words, 0)),
            lit_neg_c(Znth(1, cn_words, 0)), Mstage2, lvl, cn_sel) *
          store(&(s->size), cn_n) *
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
          store(clause_out, clause *, 0) *
          has_permission(&endvar) * has_permission(&c) * has_permission(&i)
     */
    /*@ Given watch_cap01 */
    if (vecp_reserve(watch1) == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        /*@ Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
                   clause_out == clause_out@pre &&
                   clause_new_post_at_root(s, begin, clause_out, lvl, cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_words, -2, cn_sel, cn_wl, cn_root) *
                    has_permission(&endvar) *
                    has_permission(&size) * has_permission(&watch0) *
                    has_permission(&watch1) * has_permission(&c) *
                    has_permission(&i) * has_permission(&learnt) *
                    has_permission(&database) */
        return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    /*@ Assert exists Mstage3 watch_cap11, 0 <= cn_sel && cn_sel <= 1 &&
          s == s@pre && begin == begin@pre &&
          clause_out == clause_out@pre &&
          size == Zlength(cn_words) && learnt == cn_sel &&
          Mstage3 == msolver_with_clause_caps_gen(
            cn_M, learnt_cap1,
            replace_Znth(
              lit_neg_c(Znth(1, cn_words, 0)), watch_cap11,
              replace_Znth(
                lit_neg_c(Znth(0, cn_words, 0)), watch_cap01,
                ms_wcaps(cn_M))), cn_sel) &&
          clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, Mstage3, cn_words, cn_sel, cn_root) &&
          clause_new_reserved_rooms_gen(3, cn_words, Mstage3, cn_sel) &&
          database == solver_selected_vec(s, cn_sel) &&
          watch0 == vecp_slot(cn_wl, lit_neg_c(Znth(0, cn_words, 0))) &&
          watch1 == vecp_slot(cn_wl, lit_neg_c(Znth(1, cn_words, 0))) &&
          watch_words0 ==
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wm(Mstage3), nil) &&
          watch_words1 ==
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wm(Mstage3), nil) &&
          lit_neg_c(Znth(0, cn_words, 0)) !=
            lit_neg_c(Znth(1, cn_words, 0)) &&
          vecp_rep(database, db_words(solver_selected_db(cn_sel, Mstage3)),
                   solver_selected_cap(cn_sel, Mstage3)) *
          vecp_rep(watch0,
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wm(Mstage3), nil),
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wcaps(Mstage3), 1)) *
          vecp_rep(watch1,
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wm(Mstage3), nil),
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wcaps(Mstage3), 1)) *
          clause_db_rep(solver_selected_db(cn_sel, Mstage3)) *
          clause_new_transaction_rest_at_gen(
            s, cn_wl,
            lit_neg_c(Znth(0, cn_words, 0)),
            lit_neg_c(Znth(1, cn_words, 0)), Mstage3, lvl, cn_sel) *
          store(&(s->size), cn_n) *
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
          store(clause_out, clause *, 0) *
          has_permission(&endvar) * has_permission(&c) * has_permission(&i)
     */
    /*@ Given Mstage3 */
    /*@ 0 <= cn_sel && cn_sel <= 1 && clause_new_reserved_rooms_gen(3, cn_words, Mstage3, cn_sel)
        which implies
          Zlength(db_words(solver_selected_db(cn_sel, Mstage3))) <
            solver_selected_cap(cn_sel, Mstage3) &&
          Zlength(Znth(lit_neg_c(Znth(0, cn_words, 0)),
                       ms_wm(Mstage3), nil)) <
            Znth(lit_neg_c(Znth(0, cn_words, 0)), ms_wcaps(Mstage3), 1) &&
          Zlength(Znth(lit_neg_c(Znth(1, cn_words, 0)),
                       ms_wm(Mstage3), nil)) <
            Znth(lit_neg_c(Znth(1, cn_words, 0)), ms_wcaps(Mstage3), 1)
     */

    c = minisat_clause_alloc(size);
    /*@ 0 <= cn_sel && cn_sel <= 1 && clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, Mstage3, cn_words, cn_sel, cn_root) &&
          MiniSatClause::undef(c, size) *
          clause_db_rep(solver_selected_db(cn_sel, Mstage3)) *
          clause_new_transaction_rest_at_gen(
            s, cn_wl,
            lit_neg_c(Znth(0, cn_words, 0)),
            lit_neg_c(Znth(1, cn_words, 0)), Mstage3, lvl, cn_sel)
        which implies
          clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, Mstage3, cn_words, cn_sel, cn_root) &&
          clause_allocator_fresh(Mstage3, c) &&
          MiniSatClause::undef(c, size) *
          clause_db_rep(solver_selected_db(cn_sel, Mstage3)) *
          clause_new_transaction_rest_at_gen(
            s, cn_wl,
            lit_neg_c(Znth(0, cn_words, 0)),
            lit_neg_c(Znth(1, cn_words, 0)), Mstage3, lvl, cn_sel)
     */
    /*@ 0 <= cn_sel && cn_sel <= 1 && MiniSatClause::undef(c, size)
        which implies
          0 < c && c % 2 == 0 &&
          undef_data_at(&(c->size_learnt), int) *
          undef_data_at(&(c->activity), float) *
          IntArray::undef_seg(&(c->lits), 0, size)
     */
    c->size_learnt = (size << 1) | learnt;
    assert(((unsigned int)c & 1) == 0);

    /*@ Inv Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
                   clause_out == clause_out@pre &&
                   0 <= i && i <= size &&
                   size == Zlength(cn_words) &&
                   learnt == cn_sel &&
            database == solver_selected_vec(s, cn_sel) &&
                   watch0 == vecp_slot(
                     cn_wl, lit_neg_c(Znth(0, cn_words, 0))) &&
                   watch1 == vecp_slot(
                     cn_wl, lit_neg_c(Znth(1, cn_words, 0))) &&
                   watch_words0 ==
                     Znth(lit_neg_c(Znth(0, cn_words, 0)),
                          ms_wm(Mstage3), nil) &&
                   watch_words1 ==
                     Znth(lit_neg_c(Znth(1, cn_words, 0)),
                          ms_wm(Mstage3), nil) &&
                   cn_n == ms_size(Mstage3) &&
                   2 <= Zlength(cn_words) &&
                   2 * Zlength(cn_words) + 1 <= INT_MAX &&
                   0 < c && c % 2 == 0 &&
                   clause_allocator_fresh(Mstage3, c) &&
                   clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, Mstage3, cn_words, cn_sel, cn_root) &&
                   Zlength(db_words(solver_selected_db(cn_sel, Mstage3))) <
                     solver_selected_cap(cn_sel, Mstage3) &&
                   Zlength(Znth(lit_neg_c(Znth(0, cn_words, 0)),
                                ms_wm(Mstage3), nil)) <
                     Znth(lit_neg_c(Znth(0, cn_words, 0)),
                          ms_wcaps(Mstage3), 1) &&
                   Zlength(Znth(lit_neg_c(Znth(1, cn_words, 0)),
                                ms_wm(Mstage3), nil)) <
                     Znth(lit_neg_c(Znth(1, cn_words, 0)),
                          ms_wcaps(Mstage3), 1) &&
                   store(&(c->size_learnt), size * 2 + cn_sel) *
                   undef_data_at(&(c->activity), float) *
                   IntArray::seg(&(c->lits), 0, i,
                                 sublist(0, i, cn_words)) *
                   IntArray::undef_seg(&(c->lits), i, size) *
                   vecp_rep(database, db_words(solver_selected_db(cn_sel, Mstage3)),
                            solver_selected_cap(cn_sel, Mstage3)) *
                   vecp_rep(watch0, watch_words0,
                     Znth(lit_neg_c(Znth(0, cn_words, 0)),
                          ms_wcaps(Mstage3), 1)) *
                   vecp_rep(watch1, watch_words1,
                     Znth(lit_neg_c(Znth(1, cn_words, 0)),
                          ms_wcaps(Mstage3), 1)) *
                   clause_db_rep(solver_selected_db(cn_sel, Mstage3)) *
                   clause_new_transaction_rest_at_gen(s, cn_wl,
                     lit_neg_c(Znth(0, cn_words, 0)),
                     lit_neg_c(Znth(1, cn_words, 0)), Mstage3, lvl, cn_sel) *
                   store(&(s->size), cn_n) *
                   IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
                   store(clause_out, clause *, 0) *
                   has_permission(&endvar)
     */
    for (i = 0; i < size; i++)
        c->lits[i] = begin[i];

    if (learnt)
        c->activity = 0.0f;

    /*@ Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
               clause_out == clause_out@pre &&
               i == size && size == Zlength(cn_words) && learnt == cn_sel &&
                   database == solver_selected_vec(s, cn_sel) && cn_n == ms_size(Mstage3) &&
                   watch0 == vecp_slot(
                     cn_wl, lit_neg_c(Znth(0, cn_words, 0))) &&
                   watch1 == vecp_slot(
                     cn_wl, lit_neg_c(Znth(1, cn_words, 0))) &&
                   watch_words0 ==
                     Znth(lit_neg_c(Znth(0, cn_words, 0)),
                          ms_wm(Mstage3), nil) &&
                   watch_words1 ==
                     Znth(lit_neg_c(Znth(1, cn_words, 0)),
                          ms_wm(Mstage3), nil) &&
                   2 <= Zlength(cn_words) &&
                   2 * Zlength(cn_words) + 1 <= INT_MAX &&
                   2 * cn_n <= INT_MAX &&
                   0 <= Znth(0, cn_words, 0) &&
                   Znth(0, cn_words, 0) < 2 * cn_n &&
                   0 <= Znth(1, cn_words, 0) &&
                   Znth(1, cn_words, 0) < 2 * cn_n &&
                   0 <= lit_neg_c(Znth(0, cn_words, 0)) &&
                   lit_neg_c(Znth(0, cn_words, 0)) < 2 * cn_n &&
                   0 <= lit_neg_c(Znth(1, cn_words, 0)) &&
                   lit_neg_c(Znth(1, cn_words, 0)) < 2 * cn_n &&
                   0 < c && c % 2 == 0 &&
                   clause_allocator_fresh(Mstage3, c) &&
                   clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, Mstage3, cn_words, cn_sel, cn_root) &&
                   Zlength(db_words(solver_selected_db(cn_sel, Mstage3))) <
                     solver_selected_cap(cn_sel, Mstage3) &&
                   Zlength(Znth(lit_neg_c(Znth(0, cn_words, 0)),
                                ms_wm(Mstage3), nil)) <
                     Znth(lit_neg_c(Znth(0, cn_words, 0)),
                          ms_wcaps(Mstage3), 1) &&
                   Zlength(Znth(lit_neg_c(Znth(1, cn_words, 0)),
                                ms_wm(Mstage3), nil)) <
                     Znth(lit_neg_c(Znth(1, cn_words, 0)),
                          ms_wcaps(Mstage3), 1) &&
                   MiniSatClause::rep(c, solver_selected_is_learnt(cn_sel), cn_words) *
                   vecp_rep(database, db_words(solver_selected_db(cn_sel, Mstage3)),
                            solver_selected_cap(cn_sel, Mstage3)) *
                   vecp_rep(watch0, watch_words0,
                     Znth(lit_neg_c(Znth(0, cn_words, 0)),
                          ms_wcaps(Mstage3), 1)) *
                   vecp_rep(watch1, watch_words1,
                     Znth(lit_neg_c(Znth(1, cn_words, 0)),
                          ms_wcaps(Mstage3), 1)) *
                   clause_db_rep(solver_selected_db(cn_sel, Mstage3)) *
                   clause_new_transaction_rest_at_gen(s, cn_wl,
                     lit_neg_c(Znth(0, cn_words, 0)),
                     lit_neg_c(Znth(1, cn_words, 0)), Mstage3, lvl, cn_sel) *
                   store(&(s->size), cn_n) *
                   IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
                   store(clause_out, clause *, 0) *
                   has_permission(&endvar)
     */

    assert(begin[0] >= 0);
    assert(begin[0] < s->size*2);
    assert(begin[1] >= 0);
    assert(begin[1] < s->size*2);

    assert(lit_neg(begin[0])
             /*@ where (bounded) lit_bound_n = cn_n */ < s->size*2);
    assert(lit_neg(begin[1])
             /*@ where (bounded) lit_bound_n = cn_n */ < s->size*2);

    check(vecp_push(database, c) == 1);
    check(vecp_push(watch0,
        (void *)(size > 2 ? c : clause_from_lit(begin[1]))) == 1);
    check(vecp_push(watch1,
        (void *)(size > 2 ? c : clause_from_lit(begin[0]))) == 1);
    *clause_out = c;
    /*@ Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
               clause_out == clause_out@pre &&
               clause_new_post_at_root(s, begin, clause_out, lvl, cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_words, 1, cn_sel, cn_wl, cn_root) *
                has_permission(&endvar) *
                has_permission(&size) * has_permission(&watch0) *
                has_permission(&watch1) * has_permission(&c) *
                has_permission(&i) * has_permission(&learnt) *
                has_permission(&database) */
    return 1;
}


/* Detach clause `c` from the two watcher lists that hold it, subtract it from
   the literal statistics, and free it.  Requires `c` not to be the recorded
   reason of any assigned variable; the postcondition hands back the solver
   with that clause gone from the watcher structure. */
static void clause_remove(solver* s, clause* c)
/*@ With n cap wl reasons_ptr (wm : list (list Z)) (caps : list Z)
          (is_learnt : bool) (clause_words stats0 reasons0 : list Z)
    Require clause_remove_pre(s, c, n, cap, wl, reasons_ptr, wm, caps,
                              is_learnt, clause_words, stats0, reasons0)
    Ensure clause_remove_post(s, c, n, cap, wl, reasons_ptr, wm, caps,
                              clause_words, stats0, reasons0)
 */
{
    /*@ clause_remove_pre(s, c, n, cap, wl, reasons_ptr, wm, caps,
                          is_learnt, clause_words, stats0, reasons0)
        which implies
          0 <= n && n <= cap && 2 * n <= INT_MAX &&
          0 < c && c % 2 == 0 &&
          Zlength(reasons0) == n &&
          clause_remove_ready(n, c, clause_words, wm, caps, stats0) &&
          clause_unlocked_words(c, reasons0) &&
          clause_remove_open_at(s, n, cap, wl, reasons_ptr, wm, caps,
                                stats0, reasons0) *
          store(clause_hdr_addr(c), int,
                clause_hdr_word(is_learnt, Zlength(clause_words))) *
          activity_state(c, is_learnt) *
          IntArray::seg(clause_lits_addr(c), 0, Zlength(clause_words),
                        clause_words)
     */
    lit* lits = clause_begin(c);
    /*@ Assert s == s@pre && c == c@pre &&
          lits == clause_lits_addr(c) &&
          0 <= n && n <= cap && 2 * n <= INT_MAX &&
          0 < c && c % 2 == 0 &&
          Zlength(reasons0) == n &&
          clause_remove_ready(n, c, clause_words, wm, caps, stats0) &&
          clause_unlocked_words(c, reasons0) &&
          0 <= Znth(0, clause_words, 0) &&
          Znth(0, clause_words, 0) < 2 * n &&
          0 <= Znth(1, clause_words, 0) &&
          Znth(1, clause_words, 0) < 2 * n &&
          0 <= lit_neg_c(Znth(0, clause_words, 0)) &&
          lit_neg_c(Znth(0, clause_words, 0)) < 2 * n &&
          0 <= lit_neg_c(Znth(1, clause_words, 0)) &&
          lit_neg_c(Znth(1, clause_words, 0)) < 2 * n &&
          clause_remove_open_at(s, n, cap, wl, reasons_ptr, wm, caps,
                                stats0, reasons0) *
          store(clause_hdr_addr(c), int,
                clause_hdr_word(is_learnt, Zlength(clause_words))) *
          activity_state(c, is_learnt) *
          store(lits + 0 * sizeof(int), int,
                Znth(0, clause_words, 0)) *
          store(lits + 1 * sizeof(int), int,
                Znth(1, clause_words, 0)) *
          IntArray::seg(lits, 2, Zlength(clause_words),
                        sublist(2, Zlength(clause_words), clause_words))
     */
    assert(lit_neg(lits[0]) < s->size*2);
    assert(lit_neg(lits[1]) < s->size*2);

    //vecp_remove(solver_read_wlist(s,lit_neg(lits[0])),(void*)c);
    //vecp_remove(solver_read_wlist(s,lit_neg(lits[1])),(void*)c);

    assert(lits[0] < s->size*2);
    /*@ 0 <= lit_neg_c(Znth(0, clause_words, 0)) &&
          lit_neg_c(Znth(0, clause_words, 0)) < 2 * n &&
          wlists_rep(wl, n, wm, caps)
        which implies
          wlists_focus_at(wl, lit_neg_c(Znth(0, clause_words, 0)),
                          wm, caps,
                          vecp_slot(wl,
                            lit_neg_c(Znth(0, clause_words, 0))))
     */
    vecp_remove(solver_read_wlist(s,lit_neg(lits[0]) /*@ where (original) */),
                (void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[1])))
      /*@ where vr_n = n */;
    /*@ exists found0,
          vecp_remove_found(clause_watch_word(c, clause_words,
                              Znth(1, clause_words, 0)),
                            Znth(lit_neg_c(Znth(0, clause_words, 0)),
                                 wm, nil), found0) &&
          wlists_rep(wl, n,
            replace_Znth(lit_neg_c(Znth(0, clause_words, 0)),
              vecp_remove_result(
                Znth(lit_neg_c(Znth(0, clause_words, 0)), wm, nil), found0),
              wm), caps)
     */
    /*@ Given found0 */
    /*@ 0 <= lit_neg_c(Znth(1, clause_words, 0)) &&
          lit_neg_c(Znth(1, clause_words, 0)) < 2 * n &&
          wlists_rep(wl, n,
          replace_Znth(lit_neg_c(Znth(0, clause_words, 0)),
            vecp_remove_result(
              Znth(lit_neg_c(Znth(0, clause_words, 0)), wm, nil), found0),
            wm), caps)
        which implies
          wlists_focus_at(wl, lit_neg_c(Znth(1, clause_words, 0)),
            replace_Znth(lit_neg_c(Znth(0, clause_words, 0)),
              vecp_remove_result(
                Znth(lit_neg_c(Znth(0, clause_words, 0)), wm, nil), found0),
              wm), caps,
            vecp_slot(wl, lit_neg_c(Znth(1, clause_words, 0))))
     */
    vecp_remove(solver_read_wlist(s,lit_neg(lits[1]) /*@ where (original) */),
                (void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[0])))
      /*@ where vr_n = n */;

    if (clause_learnt(c)){
        s->stats.learnts--;
        s->stats.learnts_literals -= clause_size(c);
    }else{
        s->stats.clauses--;
        s->stats.clauses_literals -= clause_size(c);
    }

    /*@ clause_lits_addr(c) == lits && 0 < c && c % 2 == 0 &&
          store(clause_hdr_addr(c), int,
              clause_hdr_word(is_learnt, Zlength(clause_words))) *
          activity_state(c, is_learnt) *
          store(lits + 0 * sizeof(int), int,
                Znth(0, clause_words, 0)) *
          store(lits + 1 * sizeof(int), int,
                Znth(1, clause_words, 0)) *
          IntArray::seg(lits, 2, Zlength(clause_words),
                        sublist(2, Zlength(clause_words), clause_words))
        which implies
          MiniSatClause::owned(c, Zlength(clause_words)) *
          has_permission(&lits)
     */
    minisat_clause_free(c);
    /*@ Assert s == s@pre && c == c@pre &&
                clause_remove_post(s, c, n, cap, wl, reasons_ptr, wm, caps,
                                  clause_words, stats0, reasons0) *
                has_permission(&lits) */
}


/* Decide whether a clause is already satisfied at the root.  Requires the
   trail-limit vector to be empty, so every assignment on the trail is a root
   assignment, and returns 1 when some literal of the clause is true under it
   and -1 otherwise.  The clause and the assignment are left unchanged. */
static lbool clause_simplify(solver* s, clause* c)
/*@ With n (clause_words assigns0 : list Z) (is_learnt : bool)
          assigns_ptr lim_cap
    Require 0 <= n && n <= INT_MAX && 2 * n <= INT_MAX &&
            Zlength(assigns0) == n && Forall(lbool_cell, assigns0) &&
            Forall(lit_wf_c(n), clause_words) &&
            0 < c && c % 2 == 0 &&
            store(&(s->assigns), assigns_ptr) *
            CharArray::seg(assigns_ptr, 0, n, assigns0) *
            store(clause_hdr_addr(c), int,
                  clause_hdr_word(is_learnt, Zlength(clause_words))) *
            activity_state(c, is_learnt) *
            IntArray::seg(clause_lits_addr(c), 0,
                          Zlength(clause_words), clause_words) *
            veci_rep(&(s->trail_lim), z_nil, lim_cap)
    Ensure clause_simplify_result(clause_words, assigns0, __return) &&
           0 < c && c % 2 == 0 &&
           store(&(s->assigns), assigns_ptr) *
           CharArray::seg(assigns_ptr, 0, n, assigns0) *
           store(clause_hdr_addr(c), int,
                 clause_hdr_word(is_learnt, Zlength(clause_words))) *
           activity_state(c, is_learnt) *
           IntArray::seg(clause_lits_addr(c), 0,
                         Zlength(clause_words), clause_words) *
           veci_rep(&(s->trail_lim), z_nil, lim_cap)
 */
/* The Require/Ensure here state MiniSatClause::rep UNFOLDED rather than via
   its usual folded form, because the sole caller solver_simplify's `&&` LHS
   needs the literal array UNFOLDED (the `*clause_begin` read) while the RHS
   needs it FOLDED, with no legal annotation point between the two conjuncts:
   unfolding here is the only repair that does not change the program text. */
{
    lit*   lits   = clause_begin(c);
    lbool* values = s->assigns;
    int i;

    /* The three regions arrive already unfolded from the Require, so
       no `which implies` opens MiniSatClause::rep here. */
    assert(solver_dlevel(s) == 0);

    /*@ Inv Assert s == s@pre && c == c@pre &&
                   lits == clause_lits_addr(c) &&
                   values == assigns_ptr &&
                   0 <= Zlength(clause_words) &&
                   0 < c && c % 2 == 0 &&
                   clause_simplify_scan_inv(n, clause_words, assigns0, i) &&
                   store(&(s->assigns), assigns_ptr) *
                   CharArray::seg(values, 0, n, assigns0) *
                   store(clause_hdr_addr(c), int,
                         clause_hdr_word(is_learnt,
                                         Zlength(clause_words))) *
                   activity_state(c, is_learnt) *
                   IntArray::seg(lits, 0,
                                 Zlength(clause_words), clause_words) *
                   veci_rep(&(s->trail_lim), z_nil, lim_cap)
     */
    for (i = 0; i < clause_size(c); i++){
        /*@ clause_simplify_scan_inv(n, clause_words, assigns0, i) &&
              0 <= i && i < Zlength(clause_words) &&
              IntArray::seg(lits, 0, Zlength(clause_words), clause_words)
            which implies
            exists current_lit,
              current_lit == Znth(i, clause_words, 0) &&
              0 <= lit_var_c(current_lit) &&
              lit_var_c(current_lit) < n &&
              store(lits + i * sizeof(int), int, current_lit) *
              IntArray::missing_i(lits, i, 0, Zlength(clause_words),
                                  clause_words)
         */
        /*@ Given current_lit */
        lbool sig = !lit_sign(lits[i]);
        /*@ 0 <= sig && sig <= 1 by local */
        sig = sig + sig - 1;
        /*@ 0 <= lit_var_c(current_lit) &&
              lit_var_c(current_lit) < n &&
              CharArray::seg(values, 0, n, assigns0)
            which implies
            exists current_value,
              current_value ==
                Znth(lit_var_c(current_lit), assigns0, 0) &&
              store(values + lit_var_c(current_lit) * sizeof(char),
                    char, current_value) *
              CharArray::missing_i(values, lit_var_c(current_lit),
                                   0, n, assigns0)
         */
        if (values[lit_var(lits[i])] == sig)
            /*@ Assert s == s@pre && c == c@pre &&
                       clause_simplify_result(
                          clause_words, assigns0,
                          1) &&
                       0 <= Zlength(clause_words) &&
                       0 < c && c % 2 == 0 &&
                       store(&(s->assigns), assigns_ptr) *
                       CharArray::seg(assigns_ptr, 0, n, assigns0) *
                       store(clause_hdr_addr(c), int,
                             clause_hdr_word(is_learnt,
                                             Zlength(clause_words))) *
                       activity_state(c, is_learnt) *
                       IntArray::seg(clause_lits_addr(c), 0,
                                     Zlength(clause_words), clause_words) *
                       veci_rep(&(s->trail_lim), z_nil, lim_cap) *
                       has_permission(&lits) * has_permission(&values) *
                       has_permission(&i) * has_permission(&sig)
             */
            return MINISAT_QCP_ONE_VALUE;
    }
    /*@ Assert s == s@pre && c == c@pre &&
               clause_simplify_result(
                  clause_words, assigns0,
                  -1) &&
               0 <= Zlength(clause_words) &&
               0 < c && c % 2 == 0 &&
               store(&(s->assigns), assigns_ptr) *
               CharArray::seg(assigns_ptr, 0, n, assigns0) *
               store(clause_hdr_addr(c), int,
                     clause_hdr_word(is_learnt, Zlength(clause_words))) *
               activity_state(c, is_learnt) *
               IntArray::seg(clause_lits_addr(c), 0,
                             Zlength(clause_words), clause_words) *
               veci_rep(&(s->trail_lim), z_nil, lim_cap) *
               has_permission(&lits) * has_permission(&values) *
               has_permission(&i)
     */
    return -MINISAT_QCP_NEGATIVE_ONE_MAGNITUDE;
}

//=================================================================================================
// Minor (solver) functions:

/* Grow the solver to hold at least `n` variables: reallocate every
   per-variable array when the capacity is too small, then initialise each new
   variable as unassigned, at level zero, with no reason, and push it onto the
   order heap.  Returns 1, or -2 when a growth step cannot allocate, leaving a
   consistent solver at whatever size it had reached. */
int solver_setnvars(solver* s, int n)
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
          veci_rep(&(s->order), ms_order(sn_M), ms_order_cap(sn_M)) *
          setnvars_frame_at(s, sn_M)
     */
    /*@ Given wl act asg opos rsn lvl trl tgs */
    int new_cap = s->cap;
    int var;

    if (new_cap < n) {
        /*@ Inv Assert
              s == s@pre && n == n@pre &&
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
          veci_rep(&(s->order), ms_order(sn_M), ms_order_cap(sn_M)) *
          setnvars_frame_at(s, sn_M)
         */
        while (new_cap < n) {
            int next_cap;
            if (minisat_next_capacity(new_cap, &next_cap) ==
                -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
                return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
            new_cap = next_cap;
        }

        /* The eight bare reallocs become contracted growth shims.  A raw realloc
           has no separation-logic contract: it must be told the OLD block it
           consumes, and here that block is `seg 0..size ** undef_seg size..cap`,
           a shape none of the existing vector helpers accept (they all require
           size == cap).  The trail is the one array whose live prefix is qtail
           rather than size.  See shims-evidence/README.md. */
        s->wlists   = (vecp *)   minisat_vecp_array_grow(s->wlists, s->size, s->cap, new_cap);
        s->activity = (double *) minisat_double_array_grow(s->activity, s->size, s->cap, new_cap);
        s->assigns  = (lbool *)  minisat_char_array_grow(s->assigns, s->size, s->cap, new_cap);
        s->orderpos = (int *)    minisat_int_array_grow(s->orderpos, s->size, s->cap, new_cap);
        s->reasons  = (clause **)minisat_ptr_array_grow((void **)s->reasons, s->size, s->cap, new_cap);
        s->levels   = (int *)    minisat_int_array_grow(s->levels, s->size, s->cap, new_cap);
        s->tags     = (lbool *)  minisat_char_array_grow(s->tags, s->size, s->cap, new_cap);
        s->trail    = (lit *)    minisat_int_array_grow(s->trail, s->qtail, s->cap, new_cap);
        s->cap = new_cap;
    }

    /*@ Inv Assert exists Mcur wlc actc asgc oposc rsnc lvlc trlc tgsc,
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
          store(&(s->size), int, var) *
          store(&(s->cap), int, ms_cap(Mcur)) *
          setnvars_arrays_at(s, Mcur, var,
                             wlc, actc, asgc, oposc, rsnc, lvlc, trlc, tgsc) *
          veci_rep(&(s->order), ms_order(Mcur), ms_order_cap(Mcur)) *
          setnvars_frame_at(s, Mcur)
     */
    for (var = s->size; var < n; var++) {
        /*@ Given Mcur wlc actc */
        if (veci_reserve(&s->order) == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) {
            s->size = var;
            return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
        }
        /*@ 2 * var + 1 < 2 * ms_cap(Mcur) && 0 <= var &&
              store(&(s->wlists), vecp *, wlc) *
              wlists_undef(wlc, 2*var, 2 * ms_cap(Mcur))
            which implies
              store(&(s->wlists), vecp *, wlc) *
              undef_data_at(&(s->wlists[2*var].size), int) *
              undef_data_at(&(s->wlists[2*var].cap), int) *
              undef_data_at(&(s->wlists[2*var].ptr), void **) *
              wlists_undef(wlc, 2*var + 1, 2 * ms_cap(Mcur))
         */
        vecp_new(&s->wlists[2*var]);
        /*@ 2 * var + 1 < 2 * ms_cap(Mcur) && 0 <= var &&
              store(&(s->wlists), vecp *, wlc) *
              wlists_undef(wlc, 2*var+1, 2 * ms_cap(Mcur))
            which implies
              store(&(s->wlists), vecp *, wlc) *
              undef_data_at(&(s->wlists[2*var+1].size), int) *
              undef_data_at(&(s->wlists[2*var+1].cap), int) *
              undef_data_at(&(s->wlists[2*var+1].ptr), void **) *
              wlists_undef(wlc, 2*var + 2, 2 * ms_cap(Mcur))
         */
        vecp_new(&s->wlists[2*var+1]);
        /*@ 0 <= var && var < ms_cap(Mcur) &&
              store(&(s->activity), double *, actc) *
              DoubleArray::undef_seg(actc, var, ms_cap(Mcur))
            which implies
              store(&(s->activity), double *, actc) *
              undef_data_at(&(s->activity[var]), double) *
              DoubleArray::undef_seg(actc, var + 1, ms_cap(Mcur))
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
        s->assigns  [var] = MINISAT_QCP_ZERO_VALUE;
        s->orderpos [var] = veci_size(&s->order);
        s->reasons  [var] = (clause*)0;
        s->levels   [var] = 0;
        s->tags     [var] = MINISAT_QCP_ZERO_VALUE;

        check(veci_push(&s->order, var) == 1);
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
        s->size = var + 1;
    }
    return 1;
}


/* Assign literal `l` at the current decision level with `reason` as its
   antecedent.  If the variable already has a value nothing changes and the
   result says whether that value agrees with `l`; otherwise `l` is made true,
   pushed on the trail, and 1 is returned. */
static inline bool enqueue(solver* s, lit l, clause* reason)
/*@ With asg lvl n cap qtail l0
          (assigns levels0 reasons0 trail lim : list Z) lim_cap
    Require l == l0 &&
            enqueue_state_at(s, asg, lvl, n, cap, qtail,
                             assigns, levels0, reasons0, trail, lim, lim_cap) &&
            enqueue_input(n, l0, qtail, assigns, levels0,
                          reasons0, trail)
    Ensure enqueue_post_at(s, asg, lvl, l0, reason,
                           n, cap, qtail, __return,
                           assigns, levels0, reasons0, trail, lim, lim_cap)
 */
{
    /*@ enqueue_state_at(s, asg, lvl, n, cap, qtail,
                         assigns, levels0, reasons0, trail, lim, lim_cap)
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
          CharArray::undef_seg(asg, n, cap) *
          IntArray::seg(lvl, 0, n, levels0) *
          IntArray::undef_seg(lvl, n, cap) *
          PtrArray::seg(rsn, 0, n, reasons0) *
          PtrArray::undef_seg(rsn, n, cap) *
          IntArray::seg(trl, 0, qtail, trail) *
          IntArray::undef_seg(trl, qtail, cap) *
          veci_rep(&(s->trail_lim), lim, lim_cap)
     */
    /*@ Given rsn trl */
    lbool* values = s->assigns;
    int    v      = lit_var(l);
    /*@ v == lit_var_c(l0) by local */
    /*@ enqueue_input(n, l0, qtail, assigns, levels0, reasons0,
                      trail) &&
          CharArray::seg(asg, 0, n, assigns)
        which implies
          enqueue_input(n, l0, qtail, assigns, levels0, reasons0,
                        trail) &&
          0 <= lit_var_c(l0) && lit_var_c(l0) < n &&
          store(pointer_offset(asg, lit_var_c(l0), sizeof(char), char),
                char, Znth(lit_var_c(l0), assigns, 0)) *
          CharArray::missing_i(
            asg, lit_var_c(l0), 0, n, assigns)
     */
    /* Upstream spells this `values[v]`, and so must QCP: `v` carries the
       `v == lit_var_c(l0)` local fact, whereas re-evaluating `lit_var(l)`
       mints an atom tied to `l@pre`.  QCP has no congruence closure, so
       `l@pre == l0` does NOT transport the `0 <= lit_var_c(l0) < n` bound
       onto it, and the read is rejected as unproven. */
    lbool  val    = values[v];
#ifdef VERBOSEDEBUG
    printf(L_IND"enqueue("L_LIT")\n", L_ind, L_lit(l));
#endif

    lbool sig = !lit_sign(l);
    /*@ 0 <= sig && sig <= 1 by local */
    sig = sig + sig - 1;
    if (val != MINISAT_QCP_ZERO_VALUE){
        /*@ Assert s == s@pre && reason == reason@pre &&
                   ((val == sig &&
                      enqueue_post_at(s, asg, lvl, l0, reason,
                        n, cap, qtail, 1, assigns, levels0, reasons0,
                        trail, lim, lim_cap)) ||
                    (val != sig &&
                      enqueue_post_at(s, asg, lvl, l0, reason,
                        n, cap, qtail, 0, assigns, levels0, reasons0,
                        trail, lim, lim_cap))) *
                   has_permission(&values) * has_permission(&v) *
                   has_permission(&l)
         */
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
              IntArray::undef_seg(trl, qtail, cap)
            which implies
            exists old_level old_reason,
              0 <= lit_var_c(l0) && lit_var_c(l0) < n && qtail < n &&
              old_level == Znth(lit_var_c(l0), levels0, 0) &&
              old_reason == Znth(lit_var_c(l0), reasons0, 0) &&
              store(pointer_offset(
                      lvl, lit_var_c(l0), sizeof(int), int),
                    int, old_level) *
              IntArray::missing_i(
                lvl, lit_var_c(l0), 0, n, levels0) *
              store(pointer_offset(
                      rsn, lit_var_c(l0), sizeof(clause *), clause *),
                    clause *, old_reason) *
              PtrArray::missing_i(
                rsn, lit_var_c(l0), 0, n, reasons0) *
              undef_data_at(pointer_offset(trl, qtail, sizeof(int), int),
                            int) *
              IntArray::undef_seg(trl, qtail + 1, cap)
         */
        /*@ 0 <= lit_var_c(l0) && lit_var_c(l0) < n &&
              CharArray::full(asg, n, assigns)
            which implies
              store(pointer_offset(
                      asg, lit_var_c(l0), sizeof(char), char),
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
        /*@ Assert s == s@pre && reason == reason@pre &&
              enqueue_post_at(
              s, asg, lvl, l0, reason, n, cap, qtail, 1,
              assigns, levels0, reasons0, trail, lim, lim_cap) *
              has_permission(&values) * has_permission(&v) *
              has_permission(&val) * has_permission(&sig) *
              has_permission(&levels) * has_permission(&reasons) *
              has_permission(&l)
         */
        return MINISAT_QCP_ONE_VALUE;
    }
}


/* Open a new decision level and assign `l` true in it with no antecedent.
   Requires `l`'s variable to be unassigned and room for one more level; the
   postcondition is the enqueue postcondition with the trail-limit vector
   extended by the current trail length. */
static inline void assume(solver* s, lit l)
/*@ With asg lvl n cap qtail s0 l0
          (assigns levels reasons trail lim : list Z) lim_cap
    Require s == s0 && l == l0 &&
            Znth(lit_var_c(l0), assigns, 0) == 0 &&
            Zlength(lim) < n &&
            enqueue_input(n, l0, qtail, assigns, levels,
                          reasons, trail) &&
            store(&(s->qhead), qtail) *
            enqueue_state_at(s, asg, lvl, n, cap, qtail,
                             assigns, levels, reasons, trail, lim, lim_cap)
    Ensure assume_post_at(s, asg, lvl, l0, n, cap, qtail,
                          assigns, levels, reasons, trail, lim, lim_cap)
 */
{
    /*@ store(&(s->qhead), qtail) *
          enqueue_state_at(s, asg, lvl, n, cap, qtail,
                           assigns, levels, reasons, trail, lim, lim_cap)
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
          CharArray::undef_seg(asg, n, cap) *
          IntArray::seg(lvl, 0, n, levels) *
          IntArray::undef_seg(lvl, n, cap) *
          PtrArray::seg(rsn, 0, n, reasons) *
          PtrArray::undef_seg(rsn, n, cap) *
          IntArray::seg(trl, 0, qtail, trail) *
          IntArray::undef_seg(trl, qtail, cap) *
          veci_rep(&(s->trail_lim), lim, lim_cap)
     */
    /*@ Given rsn trl */
    assert(s->qtail == s->qhead);
    /*@ 0 <= lit_var_c(l0) && lit_var_c(l0) < n &&
          CharArray::seg(asg, 0, n, assigns)
        which implies
          store(pointer_offset(asg, lit_var_c(l0), sizeof(char), char),
                char, Znth(lit_var_c(l0), assigns, 0)) *
          CharArray::missing_i(
            asg, lit_var_c(l0), 0, n, assigns)
    */
    assert(s->assigns[lit_var(l) /*@ where (zero_index)
                                      lv_asg = asg,
                                      lv_assigns = assigns */] ==
           MINISAT_QCP_ZERO_VALUE);
    /*@ Assert s0 == s@pre &&
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
          CharArray::undef_seg(asg, n, cap) *
          IntArray::seg(lvl, 0, n, levels) *
          IntArray::undef_seg(lvl, n, cap) *
          PtrArray::seg(rsn, 0, n, reasons) *
          PtrArray::undef_seg(rsn, n, cap) *
          IntArray::seg(trl, 0, qtail, trail) *
          IntArray::undef_seg(trl, qtail, cap) *
          veci_rep(&(s->trail_lim), lim, lim_cap)
     */
#ifdef VERBOSEDEBUG
    printf(L_IND"assume("L_LIT")\n", L_ind, L_lit(l));
#endif
    check(veci_push(&s->trail_lim,s->qtail)
          /*@ where l = lim, cap = lim_cap */ == 1);
    /*@ exists lim_cap_prime,
          lim_cap <= lim_cap_prime && lim_cap_prime <= INT_MAX &&
          store(&(s->qhead), qtail) *
          enqueue_state_at(
            s, asg, lvl, n, cap, qtail, assigns, levels, reasons, trail,
            app(lim, cons(qtail, nil)), lim_cap_prime)
     */
    enqueue(s,l,(clause*)0);
    /*@ Assert s == s@pre &&
               assume_post_at(s, asg, lvl, l0, n, cap, qtail,
                              assigns, levels, reasons, trail, lim, lim_cap) *
               has_permission(&l) */
}


/* Undo every assignment made above decision level `level`: clear the value and
   the antecedent of each such variable, return its variable to the order heap,
   and truncate the trail and the trail-limit vector.  Does nothing when the
   solver already sits at or below `level`. */
static inline void solver_canceluntil(solver* s, int level)
/*@ With (M : msolver) (wl : Z)
    Require solver_cancel_pre(s, level, M, wl)
    Ensure solver_cancel_post(s, level@pre, M, wl)
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
                   ms_order(M), ms_order_cap(M), wl)
     */
    /*@ Given activity_ptr assigns_ptr orderpos_ptr reasons_ptr trail_ptr */
    lit*     trail;
    lbool*   values;
    clause** reasons;
    int      bound;
    int      c;

    if (solver_dlevel(s) <= level)
        /*@ Assert s == s@pre && level == level@pre &&
                   solver_cancel_post(s, level, M, wl) *
                   has_permission(&trail) * has_permission(&values) *
                   has_permission(&reasons) * has_permission(&bound) *
                   has_permission(&c) */
        return;

    trail   = s->trail;
    values  = s->assigns;
    reasons = s->reasons;
    bound   = (veci_begin(&s->trail_lim))[level];

    /*@ Inv Assert exists (assigns_now reasons_now : list Z),
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
                   ms_order(M), ms_order_cap(M), wl)
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
        int     x  = lit_var(trail[c]);
        /*@ 0 <= x && x < ms_size(M) &&
              CharArray::seg(
                assigns_ptr, 0, ms_size(M), assigns_now)
            which implies
              store(pointer_offset(
                      assigns_ptr, x, sizeof(char), char),
                    char, Znth(x, assigns_now, 0)) *
              CharArray::missing_i(
                assigns_ptr, x, 0, ms_size(M), assigns_now)
         */
        values [x] = MINISAT_QCP_ZERO_VALUE;
        /*@ 0 <= x && x < ms_size(M) &&
              PtrArray::seg(
                reasons_ptr, 0, ms_size(M), reasons_now)
            which implies
              store(pointer_offset(
                      reasons_ptr, x, sizeof(struct clause_t *), struct clause_t *),
                    struct clause_t *, Znth(x, reasons_now, 0)) *
              PtrArray::missing_i(
                reasons_ptr, x, 0, ms_size(M), reasons_now)
         */
        reasons[x] = (clause*)0;
    }

    /*@ Inv Assert exists order_cap_now
                           (assigns_now reasons_now order_now orderpos_now
                            : list Z),
          s == s@pre && level == level@pre &&
          solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
          cancel_bound_ready(M, level) &&
          trail == trail_ptr && values == assigns_ptr &&
          reasons == reasons_ptr &&
          bound == Znth(level, mt_lim(ms_core(M)), 0) &&
          cancel_reinsert_loop_inv(M, level, c, order_cap_now,
                                   assigns_now, reasons_now,
                                   order_now, orderpos_now) &&
          solver_cancel_open_at(s, M, activity_ptr, assigns_ptr, orderpos_ptr,
                   reasons_ptr, trail, assigns_now, orderpos_now, reasons_now,
                   order_now, order_cap_now, wl)
     */
    for (c = s->qhead-1; c >= bound; c--)
        /*@ Given order_cap_now assigns_now reasons_now
                  order_now orderpos_now */
        /*@ solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
              cancel_reinsert_loop_inv(
                M, level, c, order_cap_now, assigns_now, reasons_now,
                order_now, orderpos_now) &&
              c >= Znth(level, mt_lim(ms_core(M)), 0)
            which implies
              solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
              cancel_reinsert_loop_inv(
                M, level, c, order_cap_now, assigns_now, reasons_now,
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
                order_cap_now, order_now, orderpos_now)
         */
        order_unassigned(s,lit_var(trail[c]));


    s->qtail = bound;
    s->qhead = bound;
    veci_resize(&s->trail_lim,level);
    /*@ Assert s == s@pre && level == level@pre &&
               solver_cancel_post(s, level, M, wl) *
               has_permission(&trail) * has_permission(&values) *
               has_permission(&reasons) * has_permission(&bound) *
               has_permission(&c) */
}

/* Unwind the trail all the way to the root after an allocation failure.
   Requires `level` to be zero and the solver to be in the capacity-exhausted
   state, and promises only that the formula is still the one held on entry --
   all that the out-of-capacity exit of the public entry points needs. */
static void solver_canceluntil_capacity(solver *s, int level)
/*@ With n (F : cnf) (A_arr : list literal)
          (K : solver_propagation_context) (M : msolver) (wl : Z)
    Require level == 0 &&
            solver_prepare_capacity_pre(s, n, F, A_arr, K, M, wl)
    Ensure solver_cancel_capacity_post(s, n, F, M, wl)
 */
{
    /*@ solver_prepare_capacity_pre(s, n, F, A_arr, K, M, wl)
        which implies exists (activity_ptr assigns_ptr orderpos_ptr
                              reasons_ptr trail_ptr levels_ptr : Z),
          solver_propagation_inv(n, F, A_arr, K, M) &&
          solver_capacity_exhausted(M) &&
          msolver_seed_shadow(M) &&
          solver_cancel_open_at(s, M, activity_ptr, assigns_ptr, orderpos_ptr,
                   reasons_ptr, trail_ptr, mt_assigns(ms_core(M)), ms_orderpos(M), ms_reason_words(M),
                   ms_order(M), ms_order_cap(M), wl) *
          solver_levels_slice_at(s, M, levels_ptr)
     */
    /*@ Given activity_ptr assigns_ptr orderpos_ptr reasons_ptr trail_ptr levels_ptr */
    if (solver_dlevel(s) > level) {
        int bound = veci_begin(&s->trail_lim)[level];
        int c;
        /*@ Inv Assert exists order_cap_now
                               (order_now orderpos_now : list Z),
              s == s@pre && level == level@pre &&
              solver_propagation_inv(n, F, A_arr, K, M) &&
              solver_capacity_exhausted(M) &&
              msolver_seed_shadow(M) &&
              bound == Znth(level, mt_lim(ms_core(M)), 0) &&
              capacity_reinsert_loop_inv(M, level, c, order_cap_now,
                                         order_now, orderpos_now) &&
              solver_cancel_open_at(s, M, activity_ptr, assigns_ptr, orderpos_ptr,
                   reasons_ptr, trail_ptr, mt_assigns(ms_core(M)), orderpos_now, ms_reason_words(M),
                   order_now, order_cap_now, wl) *
              solver_levels_slice_at(s, M, levels_ptr)
         */
        for (c = s->qtail - 1; c >= s->qhead && c >= bound; c--)
            /*@ Given order_cap_now order_now orderpos_now */
            /*@ solver_propagation_inv(n, F, A_arr, K, M) &&
                  capacity_reinsert_loop_inv(
                    M, level, c, order_cap_now, order_now, orderpos_now) &&
                  c >= mt_qhead(ms_core(M)) &&
                  c >= Znth(level, mt_lim(ms_core(M)), 0)
                which implies
                  c >= Znth(level, mt_lim(ms_core(M)), 0) &&
                  0 <= c && c < ms_qtail(M) &&
                  0 <= Znth(c, mt_trail(ms_core(M)), 0) &&
                  Znth(c, mt_trail(ms_core(M)), 0) <= INT_MAX &&
                  Zlength(ms_activity(M)) == ms_size(M) &&
                  order_unassigned_pre(
                    ms_size(M),
                    lit_var_c(Znth(c, mt_trail(ms_core(M)), 0)),
                    order_cap_now, order_now, orderpos_now)
             */
            order_unassigned(s, lit_var(s->trail[c]));
    }
    /*@ Assert exists order_cap_ready (order_ready orderpos_ready : list Z)
                           (Mready : msolver),
          s == s@pre && level == level@pre && level == 0 &&
          Mready == msolver_heap_project(M, orderpos_ready,
                                         order_ready, order_cap_ready) &&
          heap_covers(ms_size(Mready), msolver_heap(Mready),
                      mt_assigns(ms_core(Mready)),
                      mt_trail(ms_core(Mready)),
                      mt_qhead(ms_core(Mready))) &&
          solver_propagation_inv(n, F, A_arr, K, Mready) &&
          solver_capacity_exhausted(Mready) &&
          msolver_seed_shadow(Mready) &&
          solver_cancel_pre(s, level, Mready, wl) *
          solver_levels_slice_at(s, Mready, levels_ptr)
     */
    solver_canceluntil(s, level);
}

/* Put the solver into the state the public out-of-capacity return promises:
   unwind to the root, then republish the capacity flags so that a later call
   can resume from the same formula.  Requires, and re-establishes, the
   capacity-exhausted precondition. */
static void solver_prepare_public_capacity_exit(solver *s)
/*@ With (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M : msolver) (wl : Z)
    Require solver_prepare_capacity_pre(s, n, F, A_arr, K, M, wl)
    Ensure solver_prepare_capacity_post(s, n, F, M, wl)
 */
{
    solver_canceluntil_capacity(s, 0);
    /*@ solver_cancel_capacity_post(s, n, F, M, wl)
        which implies exists (Mcancel : msolver) qhead qtail pending_qhead
                             pending_flag root (tagged stack : list Z)
                             tagged_cap stack_cap,
          ms_cap(Mcancel) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_watch_completed(Mcancel)) &&
          solver_cancel_capacity_focus(n, F, Mcancel, qhead, qtail,
            pending_qhead, pending_flag, root, tagged, stack,
            tagged_cap, stack_cap) &&
          store(&(s->qhead), qhead) * store(&(s->qtail), qtail) *
          store(&(s->capacity_pending_qhead), pending_qhead) *
          store(&(s->capacity_root_propagation_pending), pending_flag) *
          store(&(s->root_level), root) *
          veci_rep(&(s->tagged), tagged, tagged_cap) *
          veci_rep(&(s->stack), stack, stack_cap) *
          solver_public_capacity_frame(s, Mcancel, wl)
     */
    /*@ Given Mcancel */
    if (s->qhead < s->qtail) {
        s->capacity_pending_qhead = s->qhead;
        s->capacity_root_propagation_pending = 1;
        s->qhead = s->qtail;
    } else {
        s->capacity_pending_qhead = s->qhead;
        s->capacity_root_propagation_pending = 0;
    }
    s->root_level = 0;
    veci_resize(&s->tagged, 0);
    veci_resize(&s->stack, 0);
    /*@ Assert exists published_flag,
          s == s@pre &&
          solver_capacity_publication_transition(
            n, F, Mcancel, published_flag) &&
          ms_cap(Mcancel) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_watch_completed(Mcancel)) &&
          solver_rep_wl(
            s, msolver_publish_capacity(Mcancel, published_flag), wl)
     */
}

/* Install a freshly learned clause.  A clause of two or more literals is
   allocated and watched; the asserting literal is then enqueued with the new
   clause -- or with no antecedent, for a unit -- as its reason, and the learnt
   clause's activity is bumped.  Returns 1, or -2 when it cannot be allocated. */
static int solver_record(solver *s, veci *learnt)
/*@ With levels_ptr rec_wl rec_n (rec_F : cnf) (rec_A_arr rec_A_inst : list literal) (M : msolver)
          (rec_words : list Z) words_cap
    Require solver_record_pre_at(s, learnt, levels_ptr, rec_n, rec_F, rec_A_arr, rec_A_inst,
                                 M, rec_words, words_cap, rec_wl)
    Ensure solver_record_post_at(s, learnt, levels_ptr, rec_n, rec_F, rec_A_arr, rec_A_inst,
                                 M, rec_words, words_cap, __return, rec_wl)
 */
{
    /*@ solver_record_pre_at(s, learnt, levels_ptr, rec_n, rec_F, rec_A_arr, rec_A_inst,
                             M, rec_words, words_cap, rec_wl)
        which implies exists learnt_ptr,
          1 <= Zlength(rec_words) &&
          record_clause_cert(rec_n, rec_F, M, rec_words) &&
          msolver_inv(rec_n, rec_F, rec_A_arr, rec_A_inst, M) &&
          mt_qhead(ms_core(M)) == ms_qtail(M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          solver_rep_levels_wl_at(s, M, rec_wl, levels_ptr) *
          veci_rep_at(learnt, learnt_ptr, rec_words, words_cap)
     */
    /*@ Given learnt_ptr */
    lit *begin = veci_begin(learnt);
    clause *c = (clause *)0;

    assert(veci_size(learnt) > 0);
    if (veci_size(learnt) > 1) {
        /*@ record_clause_cert(rec_n, rec_F, M, rec_words) &&
              msolver_inv(rec_n, rec_F, rec_A_arr, rec_A_inst, M) &&
              1 < Zlength(rec_words)
            which implies
              record_clause_cert(rec_n, rec_F, M, rec_words) &&
              msolver_inv(rec_n, rec_F, rec_A_arr, rec_A_inst, M) &&
              2 <= Zlength(rec_words) &&
              2 * Zlength(rec_words) + 1 <= INT_MAX &&
              Forall(lit_wf_c(rec_n), rec_words) &&
              NoDup(map(lit_var_c, rec_words))
         */
        int status = clause_new(s, begin,
                                begin + veci_size(learnt)
                                  /*@ where n = Zlength(rec_words) */, 1,
                                &s->learnts, &c)
                     /*@ where (clause_new_spec)
                           lvl = levels_ptr, cn_n = rec_n, cn_F = rec_F,
                           cn_A_arr = rec_A_arr, cn_A_inst = rec_A_inst,
                           cn_M = M, cn_words = rec_words, cn_sel = 1,
                           cn_wl = rec_wl, cn_root = ms_root_level(M) */;
        if (status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
            /*@ Assert exists Mcap,
                  s == s@pre && learnt == learnt@pre &&
                  clause_new_capacity_failure(
                    rec_n, rec_F, rec_A_arr, rec_A_inst, M, Mcap, rec_words) &&
                  store(&(begin), lit *, learnt_ptr) *
                  store(&(c), clause *, 0) *
                  store(&(status), int, -2) *
                  solver_rep_levels_wl_at(s, Mcap, rec_wl, levels_ptr) *
                  veci_rep_at(learnt, learnt_ptr, rec_words, words_cap)
            */
            return status;
        /*@ Assert exists Mclause c_new,
              s == s@pre && learnt == learnt@pre &&
              status == 1 && c == c_new &&
              record_allocated(
                rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c_new, Mclause) &&
              store(&(begin), lit *, learnt_ptr) *
              solver_rep_levels_wl_at(s, Mclause, rec_wl, levels_ptr) *
              veci_rep_at(learnt, learnt_ptr, rec_words, words_cap)
         */
    }
    /*@ Assert exists Mstage,
          s == s@pre && learnt == learnt@pre &&
          1 <= Zlength(rec_words) && Zlength(rec_words) <= words_cap &&
          0 < words_cap && words_cap <= INT_MAX &&
          record_allocated(rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          store(&(begin), lit *, learnt_ptr) *
          solver_rep_levels_wl_at(s, Mstage, rec_wl, levels_ptr) *
          store(&(learnt->size), int, Zlength(rec_words)) *
          store(&(learnt->cap), int, words_cap) *
          store(&(learnt->ptr), int *, learnt_ptr) *
          IntArray::seg(learnt_ptr, 0, Zlength(rec_words), rec_words) *
          IntArray::undef_seg(learnt_ptr, Zlength(rec_words), words_cap)
     */
    /*@ Given Mstage */
    /*@ record_allocated(rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          solver_rep_levels_wl_at(s, Mstage, rec_wl, levels_ptr)
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
            mt_trail(ms_core(Mstage)), mt_lim(ms_core(Mstage)),
            ms_lim_cap(Mstage)) *
          solver_enqueue_frame_wl(s, Mstage, rec_wl)
     */
    /*@ Given assigns_ptr */
    /*@ 1 <= Zlength(rec_words) &&
          IntArray::seg(learnt_ptr, 0, Zlength(rec_words), rec_words)
        which implies
          IntArray::missing_i(
            learnt_ptr, 0, 0, Zlength(rec_words), rec_words) *
          store(learnt_ptr, int, Znth(0, rec_words, 0))
     */
    enqueue(s, *begin, c);
    /*@ Assert s == s@pre && learnt == learnt@pre &&
          record_allocated(
            rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          store(&(begin), lit *, learnt_ptr) *
          enqueue_post_at(
          s, assigns_ptr, levels_ptr, Znth(0, rec_words, 0), c,
          ms_size(Mstage), ms_cap(Mstage), ms_qtail(Mstage), 1,
          mt_assigns(ms_core(Mstage)), mt_levels(ms_core(Mstage)),
          ms_reason_words(Mstage), mt_trail(ms_core(Mstage)),
          mt_lim(ms_core(Mstage)), ms_lim_cap(Mstage)) *
          solver_enqueue_frame_wl(s, Mstage, rec_wl) *
          veci_rep_at(learnt, learnt_ptr, rec_words, words_cap)
     */
    /*@ record_allocated(
          rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          enqueue_post_at(
          s, assigns_ptr, levels_ptr, Znth(0, rec_words, 0), c,
          ms_size(Mstage), ms_cap(Mstage), ms_qtail(Mstage), 1,
          mt_assigns(ms_core(Mstage)), mt_levels(ms_core(Mstage)),
          ms_reason_words(Mstage), mt_trail(ms_core(Mstage)),
          mt_lim(ms_core(Mstage)), ms_lim_cap(Mstage)) *
          solver_enqueue_frame_wl(s, Mstage, rec_wl)
        which implies exists Menq,
          record_enqueue_success(
            rec_n, rec_F, rec_A_arr, rec_A_inst, M, Mstage, rec_words, c, Menq) &&
          solver_rep_levels_wl_at(s, Menq, rec_wl, levels_ptr)
     */
    /*@ Given Menq */
    if (c != 0) {
        /*@ msat_fp32_nonnegative(ms_cla_inc(Menq)) &&
            solver_rep_levels_wl_at(s, Menq, rec_wl, levels_ptr)
            which implies
              msat_fp32_nonnegative(ms_cla_inc(Menq)) &&
              vecp_rep(&(s->learnts), db_words(ms_learnt(Menq)),
                       ms_learnt_cap(Menq)) *
              clause_db_rep(ms_learnt(Menq)) *
              store(&(s->cla_inc), float, ms_cla_inc(Menq)) *
              store(&(s->stats.learnts), unsigned long long,
                    stats_learnts(ms_stats(Menq))) *
              store(&(s->stats.learnts_literals), unsigned long long,
                    stats_learnts_literals(ms_stats(Menq))) *
              solver_record_finish_frame_at(s, Menq, levels_ptr, rec_wl)
         */
        act_clause_bump(s, c);
        /*@ Assert exists cla_inc1,
              s == s@pre && learnt == learnt@pre &&
              c != 0 &&
              msat_fp32_nonnegative(cla_inc1) &&
              record_enqueue_success(
                rec_n, rec_F, rec_A_arr, rec_A_inst, M, Mstage, rec_words, c, Menq) &&
              store(&(begin), lit *, learnt_ptr) *
              vecp_rep(&(s->learnts), db_words(ms_learnt(Menq)),
                       ms_learnt_cap(Menq)) *
              clause_db_rep(ms_learnt(Menq)) *
              store(&(s->cla_inc), float, cla_inc1) *
              store(&(s->stats.learnts), unsigned long long,
                    stats_learnts(ms_stats(Menq))) *
              store(&(s->stats.learnts_literals), unsigned long long,
                    stats_learnts_literals(ms_stats(Menq))) *
              solver_record_finish_frame_at(s, Menq, levels_ptr, rec_wl) *
              veci_rep_at(learnt, learnt_ptr, rec_words, words_cap)
         */
        /*@ Given cla_inc1 */
        s->stats.learnts++;
        s->stats.learnts_literals += veci_size(learnt);
        /*@ Assert exists Mstats,
              s == s@pre && learnt == learnt@pre &&
              record_finish_success(
                rec_n, rec_F, rec_A_arr, rec_A_inst, M, Menq, rec_words, c,
                cla_inc1, Mstats) &&
              store(&(begin), lit *, learnt_ptr) *
              solver_rep_levels_wl_at(s, Mstats, rec_wl, levels_ptr) *
              veci_rep_at(learnt, learnt_ptr, rec_words, words_cap)
         */
    }
    /*@ Assert exists Mout,
          s == s@pre && learnt == learnt@pre &&
          record_output(rec_n, rec_F, rec_A_arr, rec_A_inst, M, Menq, rec_words, c, Mout) &&
          store(&(begin), lit *, learnt_ptr) *
          solver_rep_levels_wl_at(s, Mout, rec_wl, levels_ptr) *
          veci_rep_at(learnt, learnt_ptr, rec_words, words_cap)
    */
    return 1;
}


/* Estimate of assigned variables, weighted by decision level.  Reads, but
   never changes, the assignment and level arrays.  The result predicate in
   the contract supplies QCP with the fp64 return type; it imposes no bound. */
static double solver_progress(solver* s)
/*@ With n (assigns0 levels0 : list Z) assigns_ptr levels_ptr
    Require 0 <= n && n <= INT_MAX && Zlength(assigns0) == n &&
            Zlength(levels0) == n &&
            store(&(s->size), n) *
            store(&(s->assigns), assigns_ptr) *
            store(&(s->levels), levels_ptr) *
            CharArray::seg(assigns_ptr, 0, n, assigns0) *
            IntArray::seg(levels_ptr, 0, n, levels0)
    Ensure msat_fp64_value(__return) &&
           store(&(s->size), n) *
           store(&(s->assigns), assigns_ptr) *
           store(&(s->levels), levels_ptr) *
           CharArray::seg(assigns_ptr, 0, n, assigns0) *
           IntArray::seg(levels_ptr, 0, n, levels0)
 */
{
    lbool*  values = s->assigns;
    int*    levels = s->levels;
    int     i;

    double  progress = 0;
    double  F        = 1.0 / s->size;
    /*@ Inv Assert exists (progress_now F_now : fp64),
                   s == s@pre &&
                   values == assigns_ptr && levels == levels_ptr &&
                   0 <= i && i <= n &&
                   store(&(s->size), n) *
                   store(&(s->assigns), assigns_ptr) *
                   store(&(s->levels), levels_ptr) *
                   CharArray::seg(assigns_ptr, 0, n, assigns0) *
                   IntArray::seg(levels_ptr, 0, n, levels0) *
                   store(&progress, double, progress_now) *
                   store(&F, double, F_now)
     */
    for (i = 0; i < s->size; i++)
        if (values[i] != MINISAT_QCP_ZERO_VALUE)
            progress += pow(F, levels[i]);
    return progress / s->size;
}

//=================================================================================================
// Major methods:

/* Whether literal `l` may be dropped from a learned clause because everything
   its antecedent rests on is already implied by the rest of the clause.  Walks
   the reason graph from `l` with an explicit stack, tagging what it visits.
   Requires `l` to be assigned below the current level with a recorded reason. */
static bool solver_lit_removable(solver* s, lit l, unsigned int minl)
/*@ With reasons_ptr levels_ptr trail_ptr tags_ptr lrm_wl
          (lrm_n : Z) (lrm_F : cnf) (lrm_A_arr : list literal)
          (lrm_K : solver_propagation_context) (M : msolver) lrm_focus
    Require solver_shape(M) &&
            analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
            msolver_seed_shadow(M) &&
            0 <= lit_var_c(l) && lit_var_c(l) < lrm_n &&
            In(lit_var_c(l), map(lit_var_c, mt_trail(ms_core(M)))) &&
            In(lit_var_c(l), ms_tagged(M)) &&
            assigned_below_current(
              msolver_view(lrm_n, M), lit_var_c(l)) &&
            Znth(lit_var_c(l), ms_reason_words(M), 0) != 0 &&
            analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
            0 <= ms_tagged_cap(M) && ms_tagged_cap(M) <= INT_MAX &&
            0 <= ms_stack_cap(M) && ms_stack_cap(M) <= INT_MAX &&
            2 * lrm_n <= INT_MAX &&
            store(&(s->reasons), reasons_ptr) *
            PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
            PtrArray::undef_seg(reasons_ptr, lrm_n, ms_cap(M)) *
            store(&(s->levels), levels_ptr) *
            IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
            IntArray::undef_seg(levels_ptr, lrm_n, ms_cap(M)) *
            solver_reason_levels_frame_at(s, M, trail_ptr, tags_ptr, lrm_wl)
    Ensure solver_lit_removable_post(
             s, l, reasons_ptr, levels_ptr, trail_ptr, tags_ptr,
             lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus, __return, lrm_wl)
 */
{
    /*@ solver_shape(M) &&
          analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
          msolver_seed_shadow(M) &&
          0 <= lit_var_c(l) && lit_var_c(l) < lrm_n &&
          0 <= minl && minl <= UINT_MAX &&
          assigned_below_current(
            msolver_view(lrm_n, M), lit_var_c(l)) &&
          Znth(lit_var_c(l), ms_reason_words(M), 0) != 0 &&
          analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
          0 <= ms_tagged_cap(M) && ms_tagged_cap(M) <= INT_MAX &&
          0 <= ms_stack_cap(M) && ms_stack_cap(M) <= INT_MAX &&
          2 * lrm_n <= INT_MAX &&
          store(&(s->reasons), reasons_ptr) *
          PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
          PtrArray::undef_seg(reasons_ptr, lrm_n, ms_cap(M)) *
          store(&(s->levels), levels_ptr) *
          IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
          IntArray::undef_seg(levels_ptr, lrm_n, ms_cap(M)) *
          solver_reason_levels_frame_at(s, M, trail_ptr, tags_ptr, lrm_wl)
        which implies exists (Croot : clause),
          analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
          msolver_seed_shadow(M) &&
          0 <= lit_var_c(l) && lit_var_c(l) < lrm_n &&
          0 <= minl && minl <= UINT_MAX && 2 * lrm_n <= INT_MAX &&
          assigned_below_current(
            msolver_view(lrm_n, M), lit_var_c(l)) &&
          Znth(lit_var_c(l), ms_reason_words(M), 0) != 0 &&
          reason_target_wf(
            lrm_n, M, lit_var_c(l),
            Znth(lit_var_c(l), ms_reason_words(M), 0), Croot) &&
          analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
          store(&(s->size), lrm_n) *
          store(&(s->reasons), reasons_ptr) *
          store(&(s->levels), levels_ptr) *
          store(&(s->tags), tags_ptr) *
          PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
          PtrArray::undef_seg(reasons_ptr, lrm_n, ms_cap(M)) *
          IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
          IntArray::undef_seg(levels_ptr, lrm_n, ms_cap(M)) *
          CharArray::seg(tags_ptr, 0, lrm_n, ms_tags(M)) *
          CharArray::undef_seg(tags_ptr, lrm_n, ms_cap(M)) *
          veci_rep(&(s->tagged), ms_tagged(M), ms_tagged_cap(M)) *
          veci_rep(&(s->stack), ms_stack(M), ms_stack_cap(M)) *
          clause_db_rep(ms_prob(M)) * clause_db_rep(ms_learnt(M)) *
          MiniSatClause::rep(ms_binary(M), msat_false, ms_binary_lits(M)) *
          solver_removable_frame_at(s, M, trail_ptr, lrm_wl)
     */
    lbool*   tags    = s->tags;
    clause** reasons = s->reasons;
    int*     levels  = s->levels;
    int      top     = veci_size(&s->tagged);

    assert(lit_var(l) >= 0 && lit_var(l) < s->size);
    /*@ 0 <= lit_var_c(l) && lit_var_c(l) < lrm_n &&
          PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M))
        which implies
          store(pointer_offset(
                  reasons_ptr, lit_var_c(l), sizeof(clause *), clause *),
                clause *,
                Znth(lit_var_c(l), ms_reason_words(M), 0)) *
          removable_reason_array_hole(
            reasons_ptr, lit_var_c(l), lrm_n, ms_reason_words(M))
     */
    assert(reasons[lit_var(l)] != 0);
    /* The read above re-spells the focused cell's address index to the temp returned by
       `lit_var(l)`, which no annotation can name.  Strategy rule 29 is built for exactly
       that (`store(pointer_offset(p, ?j, PTR), ...)` plus `infer(i == j)`) and fires when
       a consumer asks for the segment -- here the Inv Assert below.  A hand-written
       refold can only lose: its own LHS has to match the state first, and it cannot. */
    veci_resize(&s->stack,0);
    check(veci_push(&s->stack,lit_var(l)) == 1);

    /*@ Inv Assert exists tags_now tagged_now stack_now done
                          tagged_cap_now stack_cap_now,
          s == s@pre && l == l@pre && minl == minl@pre &&
          tags == tags_ptr && reasons == reasons_ptr &&
          levels == levels_ptr &&
          top == Zlength(ms_tagged(M)) &&
          analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
          msolver_seed_shadow(M) &&
          2 * lrm_n <= INT_MAX &&
          analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
          analysis_tags_exact(lrm_n, tags_now, tagged_now) &&
          incl(stack_now, map(lit_var_c, mt_trail(ms_core(M)))) &&
          In(lit_var_c(l@pre), ms_tagged(M)) &&
          removable_dfs_loop_inv(lrm_n, M, l@pre, minl@pre, ms_tagged(M),
                                  tags_now, tagged_now, stack_now, done) &&
          ms_tagged_cap(M) <= tagged_cap_now &&
          ms_stack_cap(M) <= stack_cap_now &&
          0 <= tagged_cap_now && tagged_cap_now <= INT_MAX &&
          0 <= stack_cap_now && stack_cap_now <= INT_MAX &&
          store(&(s->size), lrm_n) *
          store(&(s->reasons), reasons_ptr) *
          store(&(s->levels), levels_ptr) *
          store(&(s->tags), tags_ptr) *
          PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
          PtrArray::undef_seg(reasons_ptr, lrm_n, ms_cap(M)) *
          IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
          IntArray::undef_seg(levels_ptr, lrm_n, ms_cap(M)) *
          CharArray::seg(tags_ptr, 0, lrm_n, tags_now) *
          CharArray::undef_seg(tags_ptr, lrm_n, ms_cap(M)) *
          veci_rep(&(s->tagged), tagged_now, tagged_cap_now) *
          veci_rep(&(s->stack), stack_now, stack_cap_now) *
          clause_db_rep(ms_prob(M)) * clause_db_rep(ms_learnt(M)) *
          MiniSatClause::rep(ms_binary(M), msat_false, ms_binary_lits(M)) *
          solver_removable_frame_at(s, M, trail_ptr, lrm_wl)
     */
    while (veci_size(&s->stack) > 0){
        /*@ Given tags_now tagged_now stack_now done
                  tagged_cap_now stack_cap_now */
        clause* c;
        int v = veci_begin(&s->stack)[veci_size(&s->stack)-1];
        /*@ 0 < Zlength(stack_now) &&
              v == Znth(Zlength(stack_now) - 1, stack_now, 0)
            by local */
        /*@ removable_dfs_loop_inv(
              lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
              tagged_now, stack_now, done) &&
            analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
            0 < Zlength(stack_now) &&
            v == Znth(Zlength(stack_now) - 1, stack_now, 0)
            which implies exists (Cnext : clause),
              removable_dfs_loop_inv(
                lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
                tagged_now, stack_now, done) &&
              analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
              0 < Zlength(stack_now) &&
              v == Znth(Zlength(stack_now) - 1, stack_now, 0) &&
              0 <= v && v < lrm_n &&
              Znth(v, ms_reason_words(M), 0) != 0 &&
              removable_reason_focus(
                lrm_n, M, v, Znth(v, ms_reason_words(M), 0), Cnext)
         */
        /*@ Given Cnext */
        assert(v >= 0 && v < s->size);
        veci_resize(&s->stack,veci_size(&s->stack)-1);
        /*@ removable_dfs_loop_inv(
              lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
              tagged_now, stack_now, done) &&
            0 < Zlength(stack_now) &&
            v == Znth(Zlength(stack_now) - 1, stack_now, 0)
            which implies exists (stack_after : list Z),
              removable_dfs_loop_inv(
                lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
                tagged_now, stack_now, done) &&
              stack_after ==
                sublist(0, Zlength(stack_now) - 1, stack_now) &&
              stack_now == app(stack_after, cons(v, nil))
         */
        /*@ Given stack_after */
        /*@ 0 <= v && v < lrm_n &&
              PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M))
            which implies
              store(pointer_offset(
                      reasons_ptr, v, sizeof(clause *), clause *),
                    clause *, Znth(v, ms_reason_words(M), 0)) *
              removable_reason_array_hole(
                reasons_ptr, v, lrm_n, ms_reason_words(M))
         */
        assert(reasons[v] != 0);
        c    = reasons[v];
        /* `0 <= v` is a plain value mention: it balances the local `v` cell
           across this block and gives it back at the term the LHS bound.
           A `store(&v, int, v)` on this RHS would instead re-materialise the
           cell at a FRESH unconstrained value (`v_addr_v` in the goal file)
           and leave four downstream pure demands (wits 27/28/29/48) without
           support.  `0 <= v` is PreH-supported on both sides, so it adds no
           proof burden. */
        /*@ 0 <= v &&
              store(pointer_offset(
                      reasons_ptr, v, sizeof(struct clause_t *),
                      struct clause_t *),
                    struct clause_t *, Znth(v, ms_reason_words(M), 0)) *
              removable_reason_array_hole(
                reasons_ptr, v, lrm_n, ms_reason_words(M))
            which implies
              0 <= v &&
              PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M))
         */

        /*@ c == Znth(v, ms_reason_words(M), 0) by local */

        if (clause_is_lit(c)){
            /*@ analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                  removable_reason_focus(lrm_n, M, v, c, Cnext) &&
                  is_tag(c) == msat_true
                which implies
                  removable_reason_focus(lrm_n, M, v, c, Cnext) &&
                  is_tag(c) == msat_true &&
                  0 <= lit_var_c(tag_lit(c)) &&
                  lit_var_c(tag_lit(c)) < lrm_n
             */
            int v = lit_var(clause_read_lit(c));
            /*@ 0 <= v && v < lrm_n &&
                  CharArray::seg(tags_ptr, 0, lrm_n, tags_now)
                which implies
                  store(pointer_offset(
                          tags_ptr, v, sizeof(char), char),
                        char, Znth(v, tags_now, 0)) *
                  CharArray::missing_i(tags_ptr, v, 0, lrm_n, tags_now)
             */
            /*@ 0 <= v && v < lrm_n &&
                  IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M)))
                which implies
                  store(pointer_offset(
                          levels_ptr, v, sizeof(int), int),
                        int, Znth(v, mt_levels(ms_core(M)), 0)) *
                  IntArray::missing_i(
                    levels_ptr, v, 0, lrm_n, mt_levels(ms_core(M)))
             */
            /*@ 0 <= v && v < lrm_n &&
                  PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M))
                which implies
                  store(pointer_offset(
                          reasons_ptr, v, sizeof(struct clause_t *),
                          struct clause_t *),
                        struct clause_t *,
                        Znth(v, ms_reason_words(M), 0)) *
                  PtrArray::missing_i(
                    reasons_ptr, v, 0, lrm_n, ms_reason_words(M))
             */
            if (tags[v] == MINISAT_QCP_ZERO_VALUE && levels[v] != 0){
                if (reasons[v] != 0 && ((1U << (levels[v] & 31)) & minl)){
                    /*@ analysis_cancel_ready(
                          lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                        analysis_tags_exact(lrm_n, tags_now, tagged_now) &&
                        0 <= v && v < lrm_n &&
                        Znth(v, tags_now, 0) == 0 &&
                        Znth(v, ms_reason_words(M), 0) != 0
                        which implies exists (Cpush : clause),
                          analysis_cancel_ready(
                            lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                          analysis_tags_exact(lrm_n, tags_now, tagged_now) &&
                          0 <= v && v < lrm_n &&
                          Znth(v, tags_now, 0) == 0 &&
                          Znth(v, ms_reason_words(M), 0) != 0 &&
                          Zlength(tagged_now) < lrm_n &&
                          reason_target_wf(
                            lrm_n, M, v, Znth(v, ms_reason_words(M), 0), Cpush)
                     */
                    /*@ Given Cpush */
                    /*@ analysis_cancel_ready(
                          lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                        removable_dfs_loop_inv(
                          lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
                          tagged_now, stack_now, done) &&
                        0 < Zlength(stack_now) &&
                        stack_after ==
                          sublist(0, Zlength(stack_now) - 1, stack_now)
                        which implies
                          analysis_cancel_ready(
                            lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                          removable_dfs_loop_inv(
                            lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
                            tagged_now, stack_now, done) &&
                          Zlength(stack_after) < lrm_n &&
                          Zlength(sublist(
                            0, Zlength(stack_now) - 1,
                            app(stack_after,
                                cons(Znth(Zlength(stack_now) - 1,
                                          stack_now, 0), nil)))) < lrm_n
                     */
                    check(veci_push(&s->stack,v) == 1);
                    tags[v] = MINISAT_QCP_ONE_VALUE;
                    check(veci_push(&s->tagged,v) == 1);
                }else{
                    int* tagged = veci_begin(&s->tagged);
                    int j;
                    /*@ Inv Assert exists tags_rollback,
                          s == s@pre && l == l@pre && minl == minl@pre &&
                          tags == tags_ptr &&
                          top == Zlength(ms_tagged(M)) &&
                          0 <= j && j <= Zlength(tagged_now) &&
                          (j == Zlength(tagged_now) ||
                           (j < Zlength(tagged_now) &&
                            0 <= tagged_now[j] &&
                            tagged_now[j] < lrm_n)) &&
                          analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                          msolver_seed_shadow(M) &&
                          removable_rollback_inv(
                            lrm_n, top, j, ms_tagged(M), ms_tags(M), tags_now,
                            tagged_now, tags_rollback) &&
                          ms_tagged_cap(M) <= tagged_cap_now &&
                          ms_stack_cap(M) <= stack_cap_now &&
                          store(&(s->tags), tags_ptr) *
                          CharArray::seg(tags_ptr, 0, lrm_n, tags_rollback) *
                          CharArray::undef_seg(tags_ptr, lrm_n, ms_cap(M)) *
                          veci_rep_at(&(s->tagged), tagged, tagged_now,
                                      tagged_cap_now) *
                          store(&(s->size), lrm_n) *
                          store(&(s->reasons), reasons_ptr) *
                          store(&(s->levels), levels_ptr) *
                          PtrArray::seg(reasons_ptr, 0, lrm_n,
                                        ms_reason_words(M)) *
                          PtrArray::undef_seg(reasons_ptr, lrm_n, ms_cap(M)) *
                          IntArray::seg(levels_ptr, 0, lrm_n,
                                        mt_levels(ms_core(M))) *
                          IntArray::undef_seg(levels_ptr, lrm_n, ms_cap(M)) *
                          veci_rep(&(s->stack), stack_after,
                                   stack_cap_now) *
                          clause_db_rep(ms_prob(M)) *
                          clause_db_rep(ms_learnt(M)) *
                          MiniSatClause::rep(ms_binary(M), msat_false,
                                             ms_binary_lits(M)) *
                          has_permission(&#v) *
                          has_permission(&v) *
                          has_permission(&c) *
                          has_permission(&reasons) *
                          has_permission(&levels) *
                          solver_removable_frame_at(s, M, trail_ptr, lrm_wl)
                     */
                    for (j = top; j < veci_size(&s->tagged); j++)
                        /*@ Given tags_rollback */
                        /*@ 0 <= tagged_now[j - 0] &&
                              tagged_now[j - 0] < lrm_n &&
                              CharArray::seg(tags_ptr, 0, lrm_n, tags_rollback)
                            which implies exists old_tag,
                              store(pointer_offset(
                                      tags_ptr, tagged_now[j - 0],
                                      sizeof(char), char), char, old_tag) *
                              CharArray::missing_i(
                                tags_ptr, tagged_now[j - 0], 0, lrm_n,
                                tags_rollback)
                         */
                        tags[tagged[j]] = MINISAT_QCP_ZERO_VALUE;
                    veci_resize(&s->tagged,top);
                    return MINISAT_QCP_ZERO_VALUE;
                }
            }
        }else{
            /*@ analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                  removable_reason_focus(lrm_n, M, v, c, Cnext) &&
                  is_tag(c) == msat_false &&
                  clause_db_rep(ms_prob(M)) * clause_db_rep(ms_learnt(M))
                which implies exists (is_learnt_now : bool)
                  (clause_words : list Z),
                  is_tag(c) == msat_false &&
                  analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                  removable_reason_focus(lrm_n, M, v, c, Cnext) &&
                  Cnext == lits_denote(clause_words) &&
                  Forall(lit_wf_c(lrm_n), clause_words) &&
                  clause_hdr_word(is_learnt_now,
                    Zlength(clause_words)) / 2 == Zlength(clause_words) &&
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt_now,
                                        Zlength(clause_words))) *
                  activity_state(c, is_learnt_now) *
                  IntArray::seg(clause_lits_addr(c), 0,
                                Zlength(clause_words), clause_words) *
                  clause_db_pair_remainder(ms_prob(M), ms_learnt(M), c,
                                           is_learnt_now, clause_words)
             */
            /*@ Given is_learnt_now clause_words */
            lit*    lits = clause_begin(c);
            int     i, j;

            /*@ Inv Assert exists tags_scan tagged_scan stack_scan done_scan
                                  tagged_cap_scan stack_cap_scan,
                  s == s@pre && l == l@pre && minl == minl@pre &&
                  tags == tags_ptr && reasons == reasons_ptr &&
                  levels == levels_ptr &&
                  top == Zlength(ms_tagged(M)) &&
                  lits == clause_lits_addr(c) &&
                  clause_lits_pointer(c, lits) &&
                  c % 2 == 0 &&
                  analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                  msolver_seed_shadow(M) &&
                  2 * lrm_n <= INT_MAX &&
                  analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
                  analysis_tags_exact(lrm_n, tags_scan, tagged_scan) &&
                  incl(cons(v, stack_scan),
                       map(lit_var_c, mt_trail(ms_core(M)))) &&
                  In(lit_var_c(l@pre), ms_tagged(M)) &&
                  removable_reason_scan_inv(
                    lrm_n, M, l@pre, minl@pre, ms_tagged(M), done_scan, stack_scan,
                    tags_scan, tagged_scan, Cnext, v, c, i) &&
                  1 <= i && i <= Zlength(clause_words) &&
                  Forall(lit_wf_c(lrm_n), clause_words) &&
                  clause_hdr_word(is_learnt_now, Zlength(clause_words)) / 2 ==
                    Zlength(clause_words) &&
                  ms_tagged_cap(M) <= tagged_cap_scan &&
                  ms_stack_cap(M) <= stack_cap_scan &&
                  0 <= tagged_cap_scan && tagged_cap_scan <= INT_MAX &&
                  0 <= stack_cap_scan && stack_cap_scan <= INT_MAX &&
                  Cnext == lits_denote(clause_words) &&
                  store(&(s->size), lrm_n) *
                  store(&(s->reasons), reasons_ptr) *
                  store(&(s->levels), levels_ptr) *
                  store(&(s->tags), tags_ptr) *
                  PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
                  PtrArray::undef_seg(reasons_ptr, lrm_n, ms_cap(M)) *
                  IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
                  IntArray::undef_seg(levels_ptr, lrm_n, ms_cap(M)) *
                  CharArray::seg(tags_ptr, 0, lrm_n, tags_scan) *
                  CharArray::undef_seg(tags_ptr, lrm_n, ms_cap(M)) *
                  veci_rep(&(s->tagged), tagged_scan, tagged_cap_scan) *
                  veci_rep(&(s->stack), stack_scan, stack_cap_scan) *
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt_now,
                                        Zlength(clause_words))) *
                  activity_state(c, is_learnt_now) *
                  IntArray::seg(clause_lits_addr(c), 0,
                                Zlength(clause_words),
                                clause_words) *
                  clause_db_pair_remainder(ms_prob(M), ms_learnt(M),
                                           c, is_learnt_now, clause_words) *
                  MiniSatClause::rep(ms_binary(M), msat_false,
                                     ms_binary_lits(M)) *
                  solver_removable_frame_at(s, M, trail_ptr, lrm_wl) *
                  has_permission(&j)
             */
            for (i = 1; i < clause_size(c); i++){
                /*@ Given tags_scan tagged_scan stack_scan done_scan
                          tagged_cap_scan stack_cap_scan */
                /*@ analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                      removable_reason_scan_inv(
                        lrm_n, M, l@pre, minl@pre, ms_tagged(M), done_scan,
                        stack_scan, tags_scan, tagged_scan, Cnext, v, c, i)
                    which implies
                      analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                      removable_reason_scan_inv(
                        lrm_n, M, l@pre, minl@pre, ms_tagged(M), done_scan,
                        stack_scan, tags_scan, tagged_scan, Cnext, v, c, i) &&
                      Zlength(stack_scan) < lrm_n
                 */
                /*@ Forall(lit_wf_c(lrm_n), clause_words) &&
                      0 <= i && i < Zlength(clause_words)
                    which implies
                      Forall(lit_wf_c(lrm_n), clause_words) &&
                      0 <= i && i < Zlength(clause_words) &&
                      0 <= lit_var_c(Znth(i, clause_words, 0)) &&
                      lit_var_c(Znth(i, clause_words, 0)) < lrm_n
                 */
                int v = lit_var(lits[i]);
                /*@ 0 <= v && v < lrm_n by local */
                if (tags[v] == MINISAT_QCP_ZERO_VALUE && levels[v] != 0){
                    if (reasons[v] != 0 && ((1U << (levels[v] & 31)) & minl)){
                        /*@ analysis_cancel_ready(
                              lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                            msolver_seed_shadow(M) &&
                            analysis_tags_exact(lrm_n, tags_scan, tagged_scan) &&
                            0 <= v && v < lrm_n &&
                            Znth(v, tags_scan, 0) == 0 &&
                            Znth(v, ms_reason_words(M), 0) != 0 &&
                            Zlength(stack_scan) < lrm_n
                            which implies exists (Cpush : clause),
                              analysis_cancel_ready(
                                lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                              msolver_seed_shadow(M) &&
                              analysis_tags_exact(lrm_n, tags_scan, tagged_scan) &&
                              0 <= v && v < lrm_n &&
                              Znth(v, tags_scan, 0) == 0 &&
                              Znth(v, ms_reason_words(M), 0) != 0 &&
                              Zlength(stack_scan) < lrm_n &&
                              Zlength(tagged_scan) < lrm_n &&
                              reason_target_wf(
                                lrm_n, M, v, Znth(v, ms_reason_words(M), 0),
                                Cpush)
                         */
                        check(veci_push(&s->stack,lit_var(lits[i])) == 1);
                        tags[v] = MINISAT_QCP_ONE_VALUE;
                        check(veci_push(&s->tagged,v) == 1);
                    }else{
                        int* tagged = veci_begin(&s->tagged);
                        /*@ Inv Assert exists tags_rollback,
                              s == s@pre && l == l@pre &&
                              minl == minl@pre && tags == tags_ptr &&
                              top == Zlength(ms_tagged(M)) &&
                              0 <= j && j <= Zlength(tagged_scan) &&
                              (j == Zlength(tagged_scan) ||
                               (j < Zlength(tagged_scan) &&
                                0 <= tagged_scan[j] &&
                                tagged_scan[j] < lrm_n)) &&
                              analysis_cancel_ready(
                                lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                              msolver_seed_shadow(M) &&
                              removable_rollback_inv(
                                lrm_n, top, j, ms_tagged(M), ms_tags(M),
                                tags_scan, tagged_scan, tags_rollback) &&
                              ms_tagged_cap(M) <= tagged_cap_scan &&
                              ms_stack_cap(M) <= stack_cap_scan &&
                              store(&(s->tags), tags_ptr) *
                              CharArray::seg(tags_ptr, 0, lrm_n,
                                             tags_rollback) *
                              CharArray::undef_seg(tags_ptr, lrm_n, ms_cap(M)) *
                              veci_rep_at(&(s->tagged), tagged, tagged_scan,
                                          tagged_cap_scan) *
                              store(&(s->size), lrm_n) *
                              store(&(s->reasons), reasons_ptr) *
                              store(&(s->levels), levels_ptr) *
                              PtrArray::seg(reasons_ptr, 0, lrm_n,
                                            ms_reason_words(M)) *
                              PtrArray::undef_seg(reasons_ptr, lrm_n, ms_cap(M)) *
                              IntArray::seg(levels_ptr, 0, lrm_n,
                                            mt_levels(ms_core(M))) *
                              IntArray::undef_seg(levels_ptr, lrm_n, ms_cap(M)) *
                              veci_rep(&(s->stack), stack_scan,
                                       stack_cap_scan) *
                              store(clause_hdr_addr(c), int,
                                    clause_hdr_word(is_learnt_now,
                                      Zlength(clause_words))) *
                              store(&lits, lit *, clause_lits_addr(c)) *
                              activity_state(c, is_learnt_now) *
                              IntArray::seg(clause_lits_addr(c), 0,
                                            Zlength(clause_words),
                                            clause_words) *
                              clause_db_pair_remainder(
                                ms_prob(M), ms_learnt(M), c,
                                is_learnt_now, clause_words) *
                              MiniSatClause::rep(ms_binary(M), msat_false,
                                                 ms_binary_lits(M)) *
                              has_permission(&#v) *
                              has_permission(&v) *
                              has_permission(&i) *
                              has_permission(&reasons) *
                              has_permission(&levels) *
                              solver_removable_frame_at(s, M, trail_ptr, lrm_wl)
                         */
                        for (j = top; j < veci_size(&s->tagged); j++)
                            /*@ Given tags_rollback */
                            /*@ 0 <= tagged_scan[j - 0] &&
                                  tagged_scan[j - 0] < lrm_n &&
                                  CharArray::seg(
                                    tags_ptr, 0, lrm_n, tags_rollback)
                                which implies exists old_tag,
                                  store(pointer_offset(
                                          tags_ptr, tagged_scan[j - 0],
                                          sizeof(char), char), char, old_tag) *
                                  CharArray::missing_i(
                                    tags_ptr, tagged_scan[j - 0], 0, lrm_n,
                                    tags_rollback)
                             */
                            tags[tagged[j]] = MINISAT_QCP_ZERO_VALUE;
                        veci_resize(&s->tagged,top);
                        /*@ exists c_refold lits_refold,
                              0 < c_refold && c_refold % 2 == 0 &&
                              lits_refold == clause_lits_addr(c_refold) &&
                              clause_lits_pointer(c_refold, lits_refold) &&
                              store(&c, clause *, c_refold) *
                              store(&lits, lit *, lits_refold) *
                              store(clause_hdr_addr(c_refold), int,
                                  clause_hdr_word(is_learnt_now,
                                                  Zlength(clause_words))) *
                              activity_state(c_refold, is_learnt_now) *
                              IntArray::seg(lits_refold, 0,
                                            Zlength(clause_words),
                                            clause_words) *
                              clause_db_pair_remainder(
                                ms_prob(M), ms_learnt(M), c_refold,
                                is_learnt_now, clause_words)
                            which implies
                              MiniSatClause::rep(c_refold, is_learnt_now,
                                                 clause_words) *
                              clause_db_pair_remainder(
                                ms_prob(M), ms_learnt(M), c_refold,
                                is_learnt_now, clause_words) *
                              store(&c, clause *, c_refold) *
                              store(&lits, lit *, lits_refold)
                         */
                        return MINISAT_QCP_ZERO_VALUE;
                    }
                }
            }
            /*@ 0 < c && c % 2 == 0 &&
                  lits == clause_lits_addr(c) &&
                  clause_lits_pointer(c, lits) &&
                  store(clause_hdr_addr(c), int,
                      clause_hdr_word(is_learnt_now,
                                      Zlength(clause_words))) *
                  activity_state(c, is_learnt_now) *
                  IntArray::seg(lits, 0,
                                Zlength(clause_words),
                                clause_words) *
                  clause_db_pair_remainder(ms_prob(M), ms_learnt(M), c,
                                           is_learnt_now, clause_words)
                which implies
                  MiniSatClause::rep(c, is_learnt_now, clause_words) *
                  clause_db_pair_remainder(ms_prob(M), ms_learnt(M), c,
                                           is_learnt_now, clause_words) *
                  has_permission(&lits)
             */
        }
    }

    /*@ Assert s == s@pre && l == l@pre && minl == minl@pre &&
          solver_lit_removable_post(
          s, l, reasons_ptr, levels_ptr, trail_ptr, tags_ptr,
          lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus, 1, lrm_wl) *
          has_permission(&tags) * has_permission(&reasons) *
          has_permission(&levels) * has_permission(&top) */
    return MINISAT_QCP_ONE_VALUE;
}

/* First-UIP conflict analysis.  Starting from the conflicting clause `c`, it
   resolves against the antecedents of current-level literals until one such
   literal is left, drops the literals `solver_lit_removable` shows redundant,
   and writes the result into `learnt` with the asserting literal first.  Every
   variable it touches has its activity bumped. */
static void solver_analyze(solver* s, clause* c, veci* learnt)
/*@ With (anz_n : Z) (anz_F : cnf) (anz_A_arr : list literal)
          (K : solver_propagation_context) (M : msolver) anz_focus
          (C : clause) anz_learnt_cap levels_ptr anz_wl
    Require solver_analyze_pre(
              s, c, learnt, levels_ptr, anz_n, anz_F, anz_A_arr, K, M, anz_focus,
              C, anz_learnt_cap, anz_wl)
    Ensure solver_analyze_post(
             s, learnt, levels_ptr, anz_n, anz_F, anz_A_arr, K, M, anz_focus, anz_wl)
 */
{
    /*@ solver_analyze_pre(
          s, c, learnt, levels_ptr, anz_n, anz_F, anz_A_arr, K, M, anz_focus,
          C, anz_learnt_cap, anz_wl)
        which implies exists reasons_ptr trail_ptr tags_ptr,
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, M, anz_focus) &&
          propagation_conflict_cert(anz_n, anz_F, M, C) &&
          conflict_ptr_denotes(M, c, C) &&
          msolver_seed_shadow(M) &&
          ms_root_level(M) < Zlength(mt_lim(ms_core(M))) &&
          ms_tags(M) == repeat_Z(0, anz_n) &&
          ms_tagged(M) == nil && 2 * anz_n <= INT_MAX &&
          Zlength(z_nil) == 0 &&
          solver_rep_analyze_at(
            s, M, reasons_ptr, levels_ptr, trail_ptr, tags_ptr, anz_wl) *
          veci_rep(learnt, z_nil, anz_learnt_cap)
     */
    /*@ Given reasons_ptr trail_ptr tags_ptr */
    /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, M, anz_focus) &&
        solver_rep_analyze_at(
          s, M, reasons_ptr, levels_ptr, trail_ptr, tags_ptr, anz_wl)
        which implies exists (activity_ptr orderpos_ptr : Z),
          solver_analyze_open_at(s, M, anz_n, activity_ptr, orderpos_ptr,
                  reasons_ptr, levels_ptr, trail_ptr, tags_ptr, anz_wl) *
          clause_db_rep(ms_prob(M)) *
          clause_db_rep(ms_learnt(M)) *
          MiniSatClause::rep(ms_binary(M), msat_false, ms_binary_lits(M))
     */
    lit*     trail   = s->trail;
    lbool*   tags    = s->tags;
    clause** reasons = s->reasons;
    int*     levels  = s->levels;
    int      cnt     = 0;
    lit      p       = -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    int      ind     = s->qtail-1;
    lit*     lits;
    int      i, j;
    unsigned int minl;
    int*     tagged;

    check(veci_push(learnt,-MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) == 1);

    /*@ exists learnt_cap0,
          veci_rep(learnt, app(z_nil, cons(-2, nil)), learnt_cap0) */
    /*@ Assert exists (Mcur : msolver)
                          (phase : analyze_resolution_phase)
                          (Ccur : clause) (words : list Z) words_cap,
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          analysis_core_equiv(M, Mcur) &&
          msolver_seed_shadow(Mcur) &&
          c != 0 &&
          analyze_resolution_loop_inv(
            anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
            words, cnt, ind, p) &&
          ms_root_level(Mcur) < Zlength(mt_lim(ms_core(Mcur))) &&
          2 * anz_n <= INT_MAX &&
          0 <= words_cap && words_cap <= INT_MAX &&
          solver_rep_analyze_at(
            s, Mcur, reasons, levels, trail, tags, anz_wl) *
          veci_rep(learnt, words, words_cap) *
          has_permission(&lits) * has_permission(&i) *
          has_permission(&j) * has_permission(&minl) *
          has_permission(&tagged)
     */
    do{
        /*@ exists (Mcur : msolver)
                              (phase : analyze_resolution_phase)
                              (Ccur : clause) (words : list Z) words_cap
                              reasons_loop trail_loop tags_loop,
              reasons == reasons_loop && trail == trail_loop &&
              tags == tags_loop &&
              analysis_core_equiv(M, Mcur) &&
              msolver_seed_shadow(Mcur) &&
              c != 0 &&
              analyze_resolution_loop_inv(
                anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                words, cnt, ind, p) &&
              ms_root_level(Mcur) < Zlength(mt_lim(ms_core(Mcur))) &&
              2 * anz_n <= INT_MAX &&
              0 <= words_cap && words_cap <= INT_MAX &&
              solver_rep_analyze_at(
                s, Mcur, reasons, levels, trail, tags, anz_wl) *
              veci_rep(learnt, words, words_cap) *
              has_permission(&lits) * has_permission(&i) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged)
         */
        /*@ Given Mcur phase Ccur words words_cap */
        /*@ ms_size(Mcur) == anz_n &&
            solver_rep_analyze_at(
              s, Mcur, reasons, levels, trail, tags, anz_wl)
            which implies exists (activity_ptr_loop orderpos_ptr_loop : Z),
              solver_shape(Mcur) && ms_size(Mcur) == anz_n &&
              solver_analyze_open_at(s, Mcur, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
              clause_db_rep(ms_prob(Mcur)) *
              clause_db_rep(ms_learnt(Mcur)) *
              MiniSatClause::rep(ms_binary(Mcur), msat_false, ms_binary_lits(Mcur))
         */
        /*@ Given activity_ptr_loop orderpos_ptr_loop */
        assert(c != 0);

        if (clause_is_lit(c)){
            /* The RHS restates the loop invariant instead of handing the cells
               of `ind` and `p` back with `store(&ind,int,ind) * store(&p,lit,p)`.
               A self-store on a `which implies` RHS re-materialises the local at
               a FRESH unconstrained value, so every fact the state holds at the
               old binder stops applying; that is what made the consuming LHS
               below and the trail-index bounds further down unprovable. */
            /*@ analyze_resolution_loop_inv(
                  anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                  words, cnt, ind, p) && is_tag(c) == msat_true
                which implies exists (S0 R0 : list Z)
                                     (learnt0 : clause) x,
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p) &&
                  phase == AnalyzeSelected && In(x, S0) &&
                  cnt + 1 == Zlength(S0) && 0 < cnt &&
                  level_of(msolver_view(anz_n, Mcur), x) ==
                    Some(current_level(msolver_view(anz_n, Mcur))) &&
                  c == Znth(x, ms_reason_words(Mcur), 0) &&
                  reason_target_wf(anz_n, Mcur, x, c, Ccur) &&
                  analyze_inv(anz_F, msolver_view(anz_n, Mcur), S0, R0,
                              learnt0) &&
                  lits_denote(tl(words)) == learnt0 &&
                  Permutation(ms_tagged(Mcur),
                              analyze_tags(S0, R0, learnt0))
             */
            /*@ Given S0 R0 learnt0 x */
            lit q = clause_read_lit(c);
            /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus) &&
                  reason_target_wf(anz_n, Mcur, x, c, Ccur) &&
                  level_of(msolver_view(anz_n, Mcur), x) ==
                    Some(current_level(msolver_view(anz_n, Mcur))) &&
                  is_tag(c) == msat_true && q == tag_lit(c)
                which implies
                  reason_target_wf(anz_n, Mcur, x, c, Ccur) &&
                  analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus) &&
                  is_tag(c) == msat_true && q == tag_lit(c) &&
                  0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                  level_of(msolver_view(anz_n, Mcur), lit_var_c(q)) ==
                    Some(current_level(msolver_view(anz_n, Mcur)))
             */
            assert(lit_var(q) >= 0 && lit_var(q) < s->size);
            /* Normalise the tags resource to `full` before the branch: the
               tagging path leaves it `full` after the element write while the
               fall-through would keep it `seg`, and the join has to match one
               shape on both paths. */
            /*@ CharArray::seg(tags, 0, anz_n, ms_tags(Mcur))
                which implies CharArray::full(tags, anz_n, ms_tags(Mcur))
             */
            if (tags[lit_var(q)] == MINISAT_QCP_ZERO_VALUE && levels[lit_var(q)] > 0){
                /*@ analyze_resolution_loop_inv(
                      anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                      words, cnt, ind, p) &&
                      0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                      Znth(lit_var_c(q), ms_tags(Mcur), 0) == 0 &&
                      2 * anz_n <= INT_MAX
                    which implies
                      analyze_resolution_loop_inv(
                        anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                        words, cnt, ind, p) &&
                      0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                      Znth(lit_var_c(q), ms_tags(Mcur), 0) == 0 &&
                      Zlength(ms_tagged(Mcur)) < anz_n &&
                      2 * anz_n <= INT_MAX
                 */
                tags[lit_var(q)] = MINISAT_QCP_ONE_VALUE;
                check(veci_push(&s->tagged,lit_var(q)) == 1);
                act_var_bump(s,lit_var(q));
                /* Name the fresh lists the three mutating steps handed back, so
                   the refold below can be written as a derivation rather than a
                   match.  These are partial assertions: they bind by matching
                   the named atoms and frame everything else. */
                /*@ exists (heap_now orderpos_now : list Z)
                           (activity_now : list fp64) var_inc_now,
                      order_heap_wf(anz_n, heap_now, orderpos_now) &&
                      Permutation(ms_order(Mcur), heap_now) &&
                      Zlength(activity_now) == anz_n &&
                      Zlength(orderpos_now) == anz_n &&
                      store(&(s->orderpos), int *, orderpos_ptr_loop) *
                      store(&(s->activity), double *, activity_ptr_loop) *
                      IntArray::seg(orderpos_ptr_loop, 0, anz_n, orderpos_now) *
                      DoubleArray::seg(activity_ptr_loop, 0, anz_n, activity_now) *
                      veci_rep(&(s->order), heap_now, ms_order_cap(Mcur)) *
                      store(&(s->var_inc), double, var_inc_now)
                 */
                /* Without the defining equation `tags_now' is only
                   length-constrained, and the element write to `tags[lit_var(q)]` above is lost
                   for every downstream obligation. */
                /*@ CharArray::full(
                      tags, anz_n,
                      replace_Znth(lit_var_c(q), 1, ms_tags(Mcur)))
                    which implies exists (tags_now : list Z),
                      tags_now ==
                        replace_Znth(lit_var_c(q), 1, ms_tags(Mcur)) &&
                      Zlength(tags_now) == anz_n &&
                      CharArray::full(tags, anz_n, tags_now)
                 */
                /*@ Given tags_now */
                /* A valid tagged binary reason puts var(q) at the selected
                   variable's current level (binary_reason_same_level).
                   Therefore this inherited generic non-current arm is
                   unreachable.  If inconsistent reason/level state reached
                   it, the native code would append the true propagator q
                   rather than the clause-side negation; the proof rejects
                   that corrupted state instead of assigning it semantics. */
                /* The level fact is restated in the tool's own array-read
                   spelling (`l[i - 0]`, matching how `levels[lit_var(q)]` is
                   evaluated) so that the path condition of the `else` arm is
                   directly contradictory and that arm is pruned.  The real
                   obligation stays here, in this implication, and is
                   discharged from `binary_reason_same_level`. */
                /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus) &&
                      level_of(msolver_view(anz_n, Mcur), lit_var_c(q)) ==
                      Some(current_level(msolver_view(anz_n, Mcur)))
                    which implies
                      level_of(msolver_view(anz_n, Mcur), lit_var_c(q)) ==
                        Some(current_level(msolver_view(anz_n, Mcur))) &&
                      analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus) &&
                      mt_levels(ms_core(Mcur))[lit_var_c(q) - 0] ==
                        Zlength(mt_lim(ms_core(Mcur)))
                 */
                if (levels[lit_var(q)] == solver_dlevel(s))
                    cnt++;
                else
                    /*@ Branch clear all */
                    check(veci_push(learnt,q) == 1);

            }
            /* The join is reached from the tagging path (fresh lists from the
               three mutating steps) and from the fall-through (state
               untouched), and both arrive UNFOLDED because the `analysis_cancel_ready` unfold above
               precedes the branch.  Naming the unfolded footprint with
               everything existentially bound matches both without needing
               branch-scoped folds; the fold back to solver_rep_analyze_at
               happens once, at the loop boundary. */
            /*@ Assert exists (words1 : list Z) cap1
                              (activity_j : list fp64)
                              (orderpos_j heap_j tags_j tagged_j : list Z)
                              var_inc_j tagged_cap_j
                              (Mtag : msolver) (S1 R1 : list Z)
                              (learnt1 : clause),
                  s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
                  Mtag == analyze_tag_step_msolver(
                            Mcur, tags_j, tagged_j, tagged_cap_j,
                            activity_j, orderpos_j, heap_j, var_inc_j) &&
                  solver_shape(Mtag) && anz_n == ms_size(Mtag) &&
                  analysis_core_equiv(M, Mtag) &&
                  analysis_core_equiv(Mcur, Mtag) &&
                  msolver_seed_shadow(Mtag) &&
                  analyze_tagged_step(
                    anz_n, anz_F, anz_A_arr, K, Mcur, Mtag, anz_focus, c, q, Ccur,
                    S0, R0, learnt0, x, S1, R1, learnt1, words1, cnt) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mtag, anz_focus, words1,
                    cnt, ind, S1, R1, learnt1) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) < anz_n &&
                  (ms_tags(Mtag)[
                     lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  0 <= ind && ind < ms_qtail(Mcur) &&
                  solver_analyze_open_at(s, Mtag, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
                  clause_db_rep(ms_prob(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur)) *
                  MiniSatClause::rep(ms_binary(Mcur), msat_false, ms_binary_lits(Mcur)) *
                  veci_rep(learnt, words1, cap1) *
                  store(&p, lit, p) * has_permission(&lits) * has_permission(&i) *
                  has_permission(&j) * has_permission(&minl) * has_permission(&tagged)
             */
            /*@ Given words1 cap1 activity_j orderpos_j heap_j tags_j
                      tagged_j var_inc_j tagged_cap_j
                      Mtag S1 R1 learnt1 */
            /* Mtag is minted by the lib-level record update
               `analyze_tag_step_msolver' at the branch-join `Assert' above
               (spelled via `Mtag', not by re-materialising the ghosts
               `activity_j'/`orderpos_j'/`heap_j'/`tags_j'/`tagged_j'/`var_inc_j'
               as spatial projections); this block performs the corresponding
               pure re-folding step. */
            /*@ Mtag == analyze_tag_step_msolver(
                          Mcur, tags_j, tagged_j, tagged_cap_j,
                          activity_j, orderpos_j, heap_j, var_inc_j) &&
                  solver_shape(Mtag) && anz_n == ms_size(Mtag) &&
                  analysis_core_equiv(M, Mtag) &&
                  analysis_core_equiv(Mcur, Mtag) &&
                  msolver_seed_shadow(Mtag) &&
                  analyze_tagged_step(
                    anz_n, anz_F, anz_A_arr, K, Mcur, Mtag, anz_focus, c, q, Ccur,
                    S0, R0, learnt0, x, S1, R1, learnt1, words1, cnt) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mtag, anz_focus, words1,
                    cnt, ind, S1, R1, learnt1) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) < anz_n &&
                  (ms_tags(Mtag)[
                     lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  0 <= ind && ind < ms_qtail(Mcur) &&
                  solver_analyze_open_at(s, Mtag, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
                  clause_db_rep(ms_prob(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur)) *
                  MiniSatClause::rep(ms_binary(Mcur), msat_false, ms_binary_lits(Mcur)) *
                  veci_rep(learnt, words1, cap1)
                which implies
                  analysis_core_equiv(M, Mtag) &&
                  analysis_core_equiv(Mcur, Mtag) &&
                  msolver_seed_shadow(Mtag) &&
                  0 <= ind && ind < ms_qtail(Mtag) &&
                  analyze_tagged_step(
                    anz_n, anz_F, anz_A_arr, K, Mcur, Mtag, anz_focus, c, q, Ccur,
                    S0, R0, learnt0, x, S1, R1, learnt1, words1, cnt) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mtag, anz_focus, words1,
                    cnt, ind, S1, R1, learnt1) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) < anz_n &&
                  (ms_tags(Mtag)[
                     lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  solver_rep_analyze_at(
                    s, Mtag, reasons, levels, trail, tags, anz_wl) *
                  veci_rep(learnt, words1, cap1)
             */
        }else{

            /*@ analyze_resolution_loop_inv(
                  anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                  words, cnt, ind, p) && is_tag(c) == msat_false && 0 < c &&
                  clause_db_rep(ms_prob(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur)) *
                  MiniSatClause::rep(ms_binary(Mcur), msat_false,
                                     ms_binary_lits(Mcur))
                which implies exists (is_learnt_now : bool)
                                     (clause_words : list Z),
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p) && 0 < c &&
                  Ccur == lits_denote(clause_words) &&
                  Forall(lit_wf_c(anz_n), clause_words) &&
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt_now,
                                        Zlength(clause_words))) *
                  activity_state(c, is_learnt_now) *
                  IntArray::seg(clause_lits_addr(c), 0,
                                Zlength(clause_words), clause_words) *
                  analysis_clause_remainder(
                    Mcur, c, is_learnt_now, clause_words)
             */
            /*@ Given is_learnt_now clause_words */

            /* Both arms carry `is_tag(c) == msat_false` across the refold so
               that `c` is mentioned as a VALUE term on the RHS.  The former
               `store(&c, clause *, c)` handed the cell back at a FRESH
               unconstrained value, which is why `act_clause_bump`'s
               `In(c, db_words(...))` Require below could not be discharged. */
            if (clause_learnt(c))
                /*@ is_learnt_now == msat_true &&
                      is_tag(c) == msat_false && 0 < c &&
                      In(c, db_words(ms_learnt(Mcur))) &&
                      msat_fp32_nonnegative(ms_cla_inc(Mcur)) &&
                      store(clause_hdr_addr(c), int,
                            clause_hdr_word(is_learnt_now,
                                            Zlength(clause_words))) *
                      activity_state(c, is_learnt_now) *
                      IntArray::seg(clause_lits_addr(c), 0,
                                    Zlength(clause_words), clause_words) *
                      analysis_clause_remainder(
                        Mcur, c, is_learnt_now, clause_words)
                    which implies
                      is_tag(c) == msat_false &&
                      0 < c && In(c, db_words(ms_learnt(Mcur))) &&
                      msat_fp32_nonnegative(ms_cla_inc(Mcur)) &&
                      clause_db_rep(ms_prob(Mcur)) *
                      clause_db_rep(ms_learnt(Mcur)) *
                      MiniSatClause::rep(ms_binary(Mcur), msat_false,
                                         ms_binary_lits(Mcur))
                 */
                /*@ Branch name learnt */
                act_clause_bump(s,c);

            /* The learnt arm refolded the clause into the databases because
               act_clause_bump requires the folded `clause_db_rep`; the
               fall-through still holds it split and cannot form the bundle.
               Refold it there too, scoped to the unnamed (fall-through)
               branch, so both arrive at the join in the same shape. */
            /*@ is_tag(c) == msat_false && 0 < c &&
                  store(clause_hdr_addr(c), int,
                      clause_hdr_word(is_learnt_now,
                                      Zlength(clause_words))) *
                  activity_state(c, is_learnt_now) *
                  IntArray::seg(clause_lits_addr(c), 0,
                                Zlength(clause_words), clause_words) *
                  analysis_clause_remainder(
                    Mcur, c, is_learnt_now, clause_words)
                $ unnamed
                which implies
                  is_tag(c) == msat_false &&
                  0 < c &&
                  clause_db_rep(ms_prob(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur)) *
                  MiniSatClause::rep(ms_binary(Mcur), msat_false,
                                     ms_binary_lits(Mcur))
             */

            /* The activity / orderpos / order-heap / tags / var_inc /
               cla_inc contents are spelled as projections of `Mact', not as
               fresh ghosts.  A fresh ghost would make this Assert trivially
               provable -- an existential absorbs whatever the state holds
               -- but it would make the FOLLOWING `which implies' block false:
               its RHS re-spells the same cells as `ms_activity(Mact)'
               etc., and nothing would link the ghost to the projection
               (`analysis_core_equiv' deliberately omits exactly these
               fields, in solver_qcp_lib.v).  The projections keep the
               obligation here, where the incoming
               state already reads `ms_activity(Mcur)' ... for five of the
               six; the sixth (`cla_inc', bumped by `act_clause_bump') is
               witnessed by `msolver_with_cla_inc_stats', defined in solver_qcp_lib.v. */
            /*@ Assert exists (Mact : msolver),
                  s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
                  analysis_core_equiv(M, Mact) &&
                  analysis_core_equiv(Mcur, Mact) &&
                  msolver_seed_shadow(Mact) &&
                  2 * anz_n <= INT_MAX &&
                  is_tag(c) == msat_false &&
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mact, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p) &&
                  ms_qtail(Mact) == ms_qtail(Mcur) &&
                  ms_cap(Mact) == ms_cap(Mcur) &&
                  solver_analyze_open_at(s, Mact, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
                  clause_db_rep(ms_prob(Mact)) *
                  clause_db_rep(ms_learnt(Mact)) *
                  MiniSatClause::rep(ms_binary(Mact), msat_false, ms_binary_lits(Mact)) *
                  veci_rep(learnt, words, words_cap) *
                  has_permission(&lits) * has_permission(&i) * has_permission(&j) *
                  has_permission(&minl) * has_permission(&tagged)
             */
            /*@ Given Mact */
            /*@ solver_analyze_open_at(s, Mact, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
                clause_db_rep(ms_prob(Mact)) *
                clause_db_rep(ms_learnt(Mact)) *
                MiniSatClause::rep(ms_binary(Mact), msat_false, ms_binary_lits(Mact)) &&
                  msolver_seed_shadow(Mact) && 2 * anz_n <= INT_MAX &&
                  is_tag(c) == msat_false &&
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mact, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p)
                which implies exists (activity_ptr_clause orderpos_ptr_clause : Z)
                                     (is_learnt2 : bool) (clause_words2 : list Z),
                  msolver_seed_shadow(Mact) && 2 * anz_n <= INT_MAX &&
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mact, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p) &&
                  is_tag(c) == msat_false &&
                  Ccur == lits_denote(clause_words2) &&
                  Forall(lit_wf_c(anz_n), clause_words2) &&
                  solver_analyze_open_at(s, Mact, anz_n, activity_ptr_clause, orderpos_ptr_clause,
                  reasons, levels, trail, tags, anz_wl) *
                  store(clause_hdr_addr(c), int, clause_hdr_word(is_learnt2, Zlength(clause_words2))) *
                  activity_state(c, is_learnt2) *
                  IntArray::seg(clause_lits_addr(c), 0, Zlength(clause_words2), clause_words2) *
                  analysis_clause_remainder( Mact, c, is_learnt2, clause_words2)
             */
            /*@ Given activity_ptr_clause orderpos_ptr_clause
                      is_learnt2 clause_words2 */

            lits = clause_begin(c);
            //printlits(lits,lits+clause_size(c)); printf("\n");
            /*@ Inv Assert exists (Mscan : msolver) (S0 R0 : list Z)
                                  (learnt0 : clause) x
                                  (Sscan Rscan : list Z)
                                  (learnt_scan : clause)
                                  (words_scan : list Z) cap_scan
                                  (activity_ptr_scan orderpos_ptr_scan : Z),
                  s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
                  analysis_core_equiv(Mact, Mscan) &&
                  analysis_core_equiv(M, Mscan) &&
                  msolver_seed_shadow(Mscan) &&
                  2 * anz_n <= INT_MAX &&
                  analyze_clause_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mact, Mscan, anz_focus, phase, Ccur, j, ind,
                    S0, R0, learnt0, x, Sscan, Rscan, learnt_scan,
                    words_scan, cnt) &&
                  ((phase == AnalyzeInitial && j == 0 && Mscan == Mact) ||
                   (phase == AnalyzeInitial && 0 < j) ||
                   (phase == AnalyzeSelected && j == 1 && Mscan == Mact) ||
                   (phase == AnalyzeSelected && 1 < j)) &&
                  Ccur == lits_denote(clause_words2) &&
                  lits == clause_lits_addr(c) &&
                  clause_lits_pointer(c, lits) &&
                  clause_hdr_word(is_learnt2,
                    Zlength(clause_words2)) / 2 == Zlength(clause_words2) &&
                  0 <= ind && ind < ms_qtail(Mscan) &&
                  0 <= j && j <= Zlength(clause_words2) &&
                  Forall(lit_wf_c(anz_n), clause_words2) &&
                  solver_analyze_open_at(s, Mscan, anz_n, activity_ptr_scan, orderpos_ptr_scan,
                  reasons, levels, trail, tags, anz_wl) *
                  veci_rep(learnt, words_scan, cap_scan) *
                  store(clause_hdr_addr(c), int, clause_hdr_word(is_learnt2, Zlength(clause_words2))) *
                  activity_state(c, is_learnt2) *
                  IntArray::seg(lits, 0, Zlength(clause_words2), clause_words2) *
                  analysis_clause_remainder( Mscan, c, is_learnt2, clause_words2) *
                  store(&p, lit, p) *
                  has_permission(&i) *
                  has_permission(&minl) *
                  has_permission(&tagged)
             */
            for (j = (p == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE ? 0 : 1); j < clause_size(c); j++){
                /*@ Given Mscan S0 R0 learnt0 x Sscan Rscan learnt_scan words_scan */
                lit q = lits[j];
                /*@ Forall(lit_wf_c(anz_n), clause_words2) &&
                      0 <= j && j < Zlength(clause_words2) &&
                      q == clause_words2[j - 0]
                    which implies
                      Forall(lit_wf_c(anz_n), clause_words2) &&
                      0 <= j && j < Zlength(clause_words2) &&
                      q == clause_words2[j - 0] &&
                      0 <= lit_var_c(q) && lit_var_c(q) < anz_n
                 */
                assert(lit_var(q) >= 0 && lit_var(q) < s->size);
                if (tags[lit_var(q)] == MINISAT_QCP_ZERO_VALUE && levels[lit_var(q)] > 0){
                    /*@ analyze_clause_scan_inv(
                          anz_n, anz_F, anz_A_arr, K, Mact, Mscan, anz_focus, phase, Ccur, j, ind,
                          S0, R0, learnt0, x, Sscan, Rscan, learnt_scan,
                          words_scan, cnt) &&
                          0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                          Znth(lit_var_c(q), ms_tags(Mscan), 0) == 0 &&
                          2 * anz_n <= INT_MAX
                        which implies
                          analyze_clause_scan_inv(
                            anz_n, anz_F, anz_A_arr, K, Mact, Mscan, anz_focus, phase,
                            Ccur, j, ind, S0, R0, learnt0, x, Sscan, Rscan,
                            learnt_scan, words_scan, cnt) &&
                          0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                          Znth(lit_var_c(q), ms_tags(Mscan), 0) == 0 &&
                          Zlength(ms_tagged(Mscan)) < anz_n &&
                          Zlength(words_scan) <= anz_n &&
                          2 * anz_n <= INT_MAX
                     */
                    tags[lit_var(q)] = MINISAT_QCP_ONE_VALUE;
                    check(veci_push(&s->tagged,lit_var(q)) == 1);
                    act_var_bump(s,lit_var(q));
                    if (levels[lit_var(q)] == solver_dlevel(s))
                        cnt++;
                    else
                        check(veci_push(learnt,q) == 1);
                }
            }
            /* This `Assert' is a FULL CUT, so it carries the semantic
               conjuncts the enclosing clause-scan loop establishes: a cut
               that only introduced `Mdone' would drop them all here, and the
               `which implies' below would then have to produce
               `analysis_core_equiv(M, Mdone)',
               `analyze_backward_scan_inv(...)' and the trail-index bounds
               out of nothing -- `solver_analyze_which_implies_wit_16' would
               hold exactly ONE hypothesis (`clause_lits_pointer') against
               seven unsupported demands, four of them stated at the havoc'd
               `ind_addr_v'.  The facts are stated HERE, where the
               scan-loop exit (`analyze_clause_scan_inv' at full prefix) is
               still ambient, so the fold below is left as what it is: a
               re-folding step. */
            /*@ exists (Mdone : msolver) (Sdone Rdone : list Z)
                       (learnt_done : clause)
                       (activity_ptr_done orderpos_ptr_done : Z)
                       (words_done : list Z) cap_done,
                  analysis_core_equiv(M, Mdone) &&
                  msolver_seed_shadow(Mdone) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mdone, anz_focus, words_done,
                    cnt, ind, Sdone, Rdone, learnt_done) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) < anz_n &&
                  (ms_tags(Mdone)[
                     lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  clause_lits_pointer(c, lits) &&
                  store(&j, int, j) *
                  solver_analyze_open_at(s, Mdone, anz_n, activity_ptr_done, orderpos_ptr_done,
                  reasons, levels, trail, tags, anz_wl) *
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt2,
                                        Zlength(clause_words2))) *
                  activity_state(c, is_learnt2) *
                  IntArray::seg(lits, 0,
                                Zlength(clause_words2), clause_words2) *
                  analysis_clause_remainder(
                    Mdone, c, is_learnt2, clause_words2) *
                  veci_rep(learnt, words_done, cap_done)
             */
            /*@ Given Mdone Sdone Rdone learnt_done
                      activity_ptr_done orderpos_ptr_done
                      words_done cap_done */
            /*@ analysis_core_equiv(M, Mdone) &&
                  msolver_seed_shadow(Mdone) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mdone, anz_focus, words_done,
                    cnt, ind, Sdone, Rdone, learnt_done) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) < anz_n &&
                  (ms_tags(Mdone)[
                     lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  clause_lits_pointer(c, lits) &&
                  store(&j, int, j) *
                  solver_analyze_open_at(s, Mdone, anz_n, activity_ptr_done, orderpos_ptr_done,
                  reasons, levels, trail, tags, anz_wl) *
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt2,
                                        Zlength(clause_words2))) *
                  activity_state(c, is_learnt2) *
                  IntArray::seg(lits, 0,
                                Zlength(clause_words2), clause_words2) *
                  analysis_clause_remainder(
                    Mdone, c, is_learnt2, clause_words2) *
                  veci_rep(learnt, words_done, cap_done)
                which implies
                  analysis_core_equiv(M, Mdone) &&
                  msolver_seed_shadow(Mdone) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mdone, anz_focus, words_done,
                    cnt, ind, Sdone, Rdone, learnt_done) &&
                  0 <= ind && ind < ms_qtail(Mdone) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) < anz_n &&
                  (ms_tags(Mdone)[
                     lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  clause_lits_pointer(c, lits) &&
                  has_permission(&j) *
                  solver_rep_analyze_at(
                    s, Mdone, reasons, levels, trail, tags, anz_wl) *
                  veci_rep(learnt, words_done, cap_done)
             */
        }

        /*@ Branch join all with Assert
            exists (Mresolved : msolver) (Sresolved Rresolved : list Z)
                          (learnt_resolved : clause)
                          (words_resolved : list Z) cap_resolved,
              s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
              analysis_core_equiv(M, Mresolved) &&
              msolver_seed_shadow(Mresolved) &&
              analyze_backward_scan_inv(
                anz_n, anz_F, anz_A_arr, K, Mresolved, anz_focus, words_resolved,
                cnt, ind, Sresolved, Rresolved, learnt_resolved) &&
              0 <= ind && ind < ms_qtail(Mresolved) &&
              0 <= lit_var_c(
                     mt_trail(ms_core(Mresolved))[ind - 0]) &&
              lit_var_c(mt_trail(ms_core(Mresolved))[ind - 0]) < anz_n &&
              (ms_tags(Mresolved)[
                 lit_var_c(mt_trail(ms_core(Mresolved))[ind - 0]) - 0] == 0 =>
               0 < ind) &&
              solver_rep_analyze_at(
                s, Mresolved, reasons, levels, trail, tags, anz_wl) *
              veci_rep(learnt, words_resolved, cap_resolved) *
              store(&p, lit, p) *
              store(&c, clause *, c) *
              has_permission(&lits) * has_permission(&i) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged)
         */
        /*@ Given Mresolved Sresolved Rresolved learnt_resolved
                  words_resolved cap_resolved */
        /*@ ms_size(Mresolved) == anz_n &&
            solver_rep_analyze_at(
              s, Mresolved, reasons, levels, trail, tags, anz_wl)
            which implies exists (activity_ptr_back orderpos_ptr_back : Z),
              solver_analyze_open_at(s, Mresolved, anz_n, activity_ptr_back, orderpos_ptr_back,
                  reasons, levels, trail, tags, anz_wl) *
              clause_db_rep(ms_prob(Mresolved)) *
              clause_db_rep(ms_learnt(Mresolved)) *
              MiniSatClause::rep(ms_binary(Mresolved), msat_false, ms_binary_lits(Mresolved))
         */
        /*@ Given activity_ptr_back orderpos_ptr_back */

        /*@ Inv Assert
              s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
              analysis_core_equiv(M, Mresolved) &&
              msolver_seed_shadow(Mresolved) &&
              analyze_backward_scan_inv(
                anz_n, anz_F, anz_A_arr, K, Mresolved, anz_focus, words_resolved,
                cnt, ind, Sresolved, Rresolved, learnt_resolved) &&
              0 <= ind && ind < ms_qtail(Mresolved) &&
              0 <= lit_var_c(
                     mt_trail(ms_core(Mresolved))[ind - 0]) &&
              lit_var_c(mt_trail(ms_core(Mresolved))[ind - 0]) < anz_n &&
              (ms_tags(Mresolved)[
                 lit_var_c(mt_trail(ms_core(Mresolved))[ind - 0]) - 0] == 0 =>
               0 < ind) &&
              solver_analyze_open_at(s, Mresolved, anz_n, activity_ptr_back, orderpos_ptr_back,
                  reasons, levels, trail, tags, anz_wl) *
              veci_rep(learnt, words_resolved, cap_resolved) *
              clause_db_rep(ms_prob(Mresolved)) *
              clause_db_rep(ms_learnt(Mresolved)) *
              MiniSatClause::rep(ms_binary(Mresolved), msat_false, ms_binary_lits(Mresolved)) *
              has_permission(&c) * has_permission(&p) *
              has_permission(&lits) * has_permission(&i) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged)
         */
        while (tags[lit_var(trail[ind])] == MINISAT_QCP_ZERO_VALUE)
            ind--;
        ind--;

        p = trail[ind+1];
        /*@ 0 <= lit_var_c(mt_trail(ms_core(Mresolved))[ind + 1 - 0]) &&
              lit_var_c(mt_trail(ms_core(Mresolved))[ind + 1 - 0]) < anz_n &&
              p == mt_trail(ms_core(Mresolved))[ind + 1 - 0]
            which implies
              0 <= lit_var_c(mt_trail(ms_core(Mresolved))[ind + 1 - 0]) &&
              lit_var_c(mt_trail(ms_core(Mresolved))[ind + 1 - 0]) < anz_n &&
              p == mt_trail(ms_core(Mresolved))[ind + 1 - 0] &&
              0 <= lit_var_c(p) && lit_var_c(p) < anz_n
         */
        c = reasons[lit_var(p)];
        cnt--;

        /*@ Branch join all with Assert
              s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
              analysis_core_equiv(M, Mresolved) &&
              msolver_seed_shadow(Mresolved) &&
              ((cnt == 0 && exists c_exit ind_exit,
                c == c_exit && ind == ind_exit &&
                analyze_resolution_exit(
                  anz_n, anz_F, anz_A_arr, K, Mresolved, anz_focus, p,
                  words_resolved)) ||
               (cnt > 0 && c != 0 && exists (Cnext : clause),
                reason_target_wf(
                  anz_n, Mresolved, lit_var_c(p), c, Cnext) &&
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mresolved, anz_focus, AnalyzeSelected,
                    c, Cnext, words_resolved, cnt, ind, p))) &&
              ms_root_level(Mresolved) <
                Zlength(mt_lim(ms_core(Mresolved))) &&
              2 * anz_n <= INT_MAX &&
              0 <= cap_resolved && cap_resolved <= INT_MAX &&
              solver_rep_analyze_at(
                s, Mresolved, reasons, levels, trail, tags, anz_wl) *
              veci_rep(learnt, words_resolved, cap_resolved) *
              has_permission(&lits) * has_permission(&i) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged)
         */

    } /*@ Inv Assert exists (Mcur : msolver)
                          (phase : analyze_resolution_phase)
                          (Ccur : clause) (words : list Z) words_cap,
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          analysis_core_equiv(M, Mcur) &&
          msolver_seed_shadow(Mcur) &&
          ((cnt == 0 && exists c_exit ind_exit,
            c == c_exit && ind == ind_exit &&
            analyze_resolution_exit(
              anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, p, words)) ||
           (cnt > 0 && c != 0 &&
            analyze_resolution_loop_inv(
              anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
              words, cnt, ind, p))) &&
          ms_root_level(Mcur) < Zlength(mt_lim(ms_core(Mcur))) &&
          2 * anz_n <= INT_MAX &&
          0 <= words_cap && words_cap <= INT_MAX &&
          solver_rep_analyze_at(
            s, Mcur, reasons, levels, trail, tags, anz_wl) *
          veci_rep(learnt, words, words_cap) *
          has_permission(&lits) * has_permission(&i) *
          has_permission(&j) * has_permission(&minl) *
          has_permission(&tagged)
     */
    while (cnt > 0);

    /*@ exists (Mresolution : msolver) (words_before : list Z)
                      cap_before,
          analysis_core_equiv(M, Mresolution) &&
          msolver_seed_shadow(Mresolution) &&
          analyze_resolution_exit(
            anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus, p, words_before) &&
          cnt == 0 && 0 <= cap_before && cap_before <= INT_MAX &&
          solver_rep_analyze_at(
            s, Mresolution, reasons, levels, trail, tags, anz_wl) *
          veci_rep(learnt, words_before, cap_before)
     */
    /*@ Given Mresolution words_before cap_before */
    /*@ analyze_resolution_exit(
          anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus, p, words_before)
        which implies
          analyze_resolution_exit(
            anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus, p, words_before) &&
          1 <= Zlength(words_before) && Zlength(words_before) <= anz_n
     */
    /*@ exists learnt_ptr_uip,
          1 <= Zlength(words_before) &&
          Zlength(words_before) <= cap_before &&
          0 < cap_before && cap_before <= INT_MAX &&
          store(&(learnt->size), int, Zlength(words_before)) *
          store(&(learnt->cap), int, cap_before) *
          store(&(learnt->ptr), int *, learnt_ptr_uip) *
          IntArray::seg(learnt_ptr_uip, 0,
                        Zlength(words_before), words_before) *
          IntArray::undef_seg(learnt_ptr_uip,
                              Zlength(words_before), cap_before)
     */
    *veci_begin(learnt) = lit_neg(p) /*@ where (original) */;
    /* Rule 36 left the focused cell at the pointer `veci_begin` returned, not
       at `learnt_ptr_uip`; bind that pointer so the merge below can name it. */
    /* `q` must be pinned HERE, while it is still an existential the spatial
       matcher can instantiate: quoting the `ptr` field alongside the arrays
       binds `q` to the field's value on the spot, and spelling the written
       word `lit_neg_c(p)` instead of a second ghost `w` leaves nothing to
       re-assert afterwards.  Asserting `q == learnt_ptr_uip && w ==
       lit_neg_c(p)` on the NEXT block instead is unprovable:
       by then both are opaque `forall`s and separating conjunction cannot
       identify two disjoint arrays. */
    /*@ exists q,
          store(&(learnt->ptr), int *, q) *
          IntArray::missing_i(q, 0, 0,
                              Zlength(words_before), words_before) *
          store(q, int, lit_neg_c(p)) *
          IntArray::undef_seg(q, Zlength(words_before), cap_before)
     */
    /*@ Given q */
    /*@ 1 <= Zlength(words_before) &&
          IntArray::missing_i(q, 0, 0,
                            Zlength(words_before), words_before) *
          store(q, int, lit_neg_c(p)) *
          IntArray::undef_seg(q, Zlength(words_before), cap_before)
        which implies
          IntArray::seg(
            q, 0,
            Zlength(replace_Znth(0, lit_neg_c(p), words_before)),
            replace_Znth(0, lit_neg_c(p), words_before)) *
          IntArray::undef_seg(
            q,
            Zlength(replace_Znth(0, lit_neg_c(p), words_before)),
            cap_before)
     */

    /*@ exists (words_uip : list Z),
          words_uip == replace_Znth(0, lit_neg_c(p), words_before) &&
          analysis_core_equiv(M, Mresolution) &&
          msolver_seed_shadow(Mresolution) &&
          analysis_cancel_ready(
            anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus) &&
          1 <= Zlength(words_uip) && Zlength(words_uip) <= anz_n &&
          Forall(lit_wf_c(anz_n), words_uip) &&
          NoDup(map(lit_var_c, words_uip)) &&
          analyze_clause_cert(anz_n, anz_F, Mresolution, words_uip) &&
          analysis_tags_exact(
            anz_n, ms_tags(Mresolution), ms_tagged(Mresolution)) &&
          incl(map(lit_var_c, words_uip), ms_tagged(Mresolution)) &&
          minimize_tag_scope(
            anz_n, Mresolution, words_uip, nil) &&
          veci_rep(learnt, words_uip, cap_before)
     */
    /*@ Given words_uip */

    lits = veci_begin(learnt);
    /* `2 * n <= INT_MAX' is the ONLY conjunct of this RHS that the LHS cannot
       supply: `solver_rep_analyze_at' carries `solver_shape' and the two cap
       bounds inside itself (in solver_qcp_lib.v), but it never mentions `n', so
       without the restatement the isolated goal has `n' as a free universal
       and the conjunct is unprovable.  Restating it here moves the obligation
       to a `_pure' goal where it is an ambient hypothesis. */
    /*@ 2 * anz_n <= INT_MAX && anz_n == ms_size(Mresolution) &&
        solver_rep_analyze_at(
          s, Mresolution, reasons, levels, trail, tags, anz_wl) *
          veci_rep_at(learnt, lits, words_uip, cap_before)
        which implies
        solver_shape(Mresolution) &&
        0 <= ms_tagged_cap(Mresolution) && ms_tagged_cap(Mresolution) <= INT_MAX &&
        0 <= ms_stack_cap(Mresolution) && ms_stack_cap(Mresolution) <= INT_MAX &&
        2 * anz_n <= INT_MAX &&
        anz_n == ms_size(Mresolution) &&
        store(&(s->reasons), reasons) *
        PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mresolution)) *
        PtrArray::undef_seg(reasons, anz_n, ms_cap(Mresolution)) *
        store(&(s->levels), levels) *
        IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mresolution))) *
        IntArray::undef_seg(levels, anz_n, ms_cap(Mresolution)) *
        solver_reason_levels_frame_at(s, Mresolution, trail, tags, anz_wl) *
        veci_rep_at(learnt, lits, words_uip, cap_before)
     */
    minl = 0;
    /*@ Inv Assert
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          solver_shape(Mresolution) &&
          0 <= ms_tagged_cap(Mresolution) && ms_tagged_cap(Mresolution) <= INT_MAX &&
          0 <= ms_stack_cap(Mresolution) && ms_stack_cap(Mresolution) <= INT_MAX &&
          2 * anz_n <= INT_MAX &&
          0 <= minl && minl <= UINT_MAX &&
          1 <= i && i <= Zlength(words_uip) &&
          Forall(lit_wf_c(anz_n), words_uip) &&
          analysis_core_equiv(M, Mresolution) &&
          msolver_seed_shadow(Mresolution) &&
          analysis_cancel_ready(
            anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus) &&
          analysis_tags_exact(
            anz_n, ms_tags(Mresolution), ms_tagged(Mresolution)) &&
          analyze_clause_cert(anz_n, anz_F, Mresolution, words_uip) &&
          incl(map(lit_var_c, words_uip), ms_tagged(Mresolution)) &&
          minimize_tag_scope(
            anz_n, Mresolution, words_uip, nil) &&
          store(&(s->reasons), reasons) *
          PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mresolution)) *
          PtrArray::undef_seg(reasons, anz_n, ms_cap(Mresolution)) *
          store(&(s->levels), levels) *
          IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mresolution))) *
          IntArray::undef_seg(levels, anz_n, ms_cap(Mresolution)) *
          solver_reason_levels_frame_at(s, Mresolution, trail, tags, anz_wl) *
          veci_rep_at(learnt, lits, words_uip, cap_before) *
          has_permission(&c) * has_permission(&cnt) *
          has_permission(&p) * has_permission(&ind) *
          has_permission(&j) *
          has_permission(&tagged)
     */
    for (i = 1; i < veci_size(learnt); i++){
        /*@ Forall(lit_wf_c(anz_n), words_uip) &&
              0 <= i && i < Zlength(words_uip)
            which implies
              Forall(lit_wf_c(anz_n), words_uip) &&
              0 <= i && i < Zlength(words_uip) &&
              0 <= lit_var_c(words_uip[i - 0]) &&
              lit_var_c(words_uip[i - 0]) < anz_n
         */
        int lev = levels[lit_var(lits[i])];
        minl    |= 1U << (lev & 31);
    }

    // simplify (full)
    j = 1;
    /*@ Inv Assert exists (Mmin : msolver) (kept removed T : list Z)
                          (words_min : list Z) cap_min minl_v,
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          analysis_core_equiv(M, Mmin) &&
          solver_shape(Mmin) &&
          0 <= ms_tagged_cap(Mmin) && ms_tagged_cap(Mmin) <= INT_MAX &&
          0 <= ms_stack_cap(Mmin) && ms_stack_cap(Mmin) <= INT_MAX &&
          2 * anz_n <= INT_MAX &&
          analysis_tags_exact(anz_n, ms_tags(Mmin), ms_tagged(Mmin)) &&
          msolver_seed_shadow(Mmin) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mmin, anz_focus) &&
          analyze_clause_cert(anz_n, anz_F, Mmin, words_uip) &&
          analyze_minimize_loop_inv(
            anz_n, Mmin, words_uip, kept, removed, words_min, T, i, j) &&
          1 <= j && j <= i && i <= Zlength(words_min) &&
          Forall(lit_wf_c(anz_n), words_uip) &&
          Forall(lit_wf_c(anz_n), words_min) &&
          incl(map(lit_var_c, words_min),
               map(lit_var_c, mt_trail(ms_core(Mmin)))) &&
          incl(map(lit_var_c, words_min), ms_tagged(Mmin)) &&
          0 <= cap_min && cap_min <= INT_MAX &&
          0 <= minl_v && minl_v <= UINT_MAX &&
          solver_rep_analyze_at(
            s, Mmin, reasons, levels, trail, tags, anz_wl) *
          veci_rep_at(learnt, lits, words_min, cap_min) *
          has_permission(&c) * has_permission(&cnt) *
          has_permission(&p) * has_permission(&ind) *
          store(&minl, unsigned int, minl_v) *
          has_permission(&tagged)
     */
    for (i = 1; i < veci_size(learnt); i++){
        /*@ Given Mmin kept removed T words_min */
        /*@ solver_shape(Mmin) &&
            analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mmin, anz_focus) &&
            solver_rep_analyze_at(
              s, Mmin, reasons, levels, trail, tags, anz_wl)
            which implies
            store(&(s->reasons), reasons) *
            PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mmin)) *
            PtrArray::undef_seg(reasons, anz_n, ms_cap(Mmin)) *
            store(&(s->levels), levels) *
            IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mmin))) *
            IntArray::undef_seg(levels, anz_n, ms_cap(Mmin)) *
            solver_reason_levels_frame_at(s, Mmin, trail, tags, anz_wl)
         */
        /*@ Forall(lit_wf_c(anz_n), words_min) &&
              0 <= i && i < Zlength(words_min)
            which implies
              Forall(lit_wf_c(anz_n), words_min) &&
              0 <= i && i < Zlength(words_min) &&
              0 <= lit_var_c(words_min[i - 0]) &&
              lit_var_c(words_min[i - 0]) < anz_n
         */
        if (reasons[lit_var(lits[i])] == 0 ||
            !solver_lit_removable(s,lits[i],minl)
              /*@ where reasons_ptr = reasons, levels_ptr = levels,
                        trail_ptr = trail, tags_ptr = tags,
                        lrm_n = anz_n, lrm_F = anz_F, lrm_A_arr = anz_A_arr, lrm_K = K,
                        M = Mmin, lrm_focus = anz_focus, lrm_wl = anz_wl */) {
            lits[j] = lits[i];
            j++;
        }
    }

    // update size of learnt + statistics
    /*@ exists (Mmin_done : msolver) (kept_done removed_done T_done : list Z)
                      (words_done : list Z) cap_done,
          analysis_core_equiv(M, Mmin_done) &&
          msolver_seed_shadow(Mmin_done) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mmin_done, anz_focus) &&
          analysis_tags_exact(anz_n, ms_tags(Mmin_done), ms_tagged(Mmin_done)) &&
          analyze_clause_cert(anz_n, anz_F, Mmin_done, words_uip) &&
          analyze_minimize_loop_inv(
            anz_n, Mmin_done, words_uip, kept_done, removed_done,
            words_done, T_done, i, j) &&
          solver_rep_analyze_at(
            s, Mmin_done, reasons, levels, trail, tags, anz_wl) *
          veci_rep_at(learnt, lits, words_done, cap_done)
     */
    /*@ Given Mmin_done kept_done removed_done T_done words_done cap_done */
    /*@ solver_rep_analyze_at(
          s, Mmin_done, reasons, levels, trail, tags, anz_wl)
        which implies
          store(&(s->stats.max_literals),
                stats_max_literals(ms_stats(Mmin_done))) *
          store(&(s->stats.tot_literals),
                stats_tot_literals(ms_stats(Mmin_done))) *
          solver_literal_stats_frame_at(
            s, Mmin_done, reasons, levels, trail, tags, anz_wl)
     */
    s->stats.max_literals += veci_size(learnt);
    veci_resize(learnt,j);
    s->stats.tot_literals += j;

    /* Refold the literal-stats split.  The two written words are bound as
       existentials rather than spelled, so the annotation does not have to
       restate symexec's wrapped 64-bit arithmetic. */
    /*@ exists max_lits tot_lits,
          store(&(s->stats.max_literals), max_lits) *
          store(&(s->stats.tot_literals), tot_lits) *
          solver_literal_stats_frame_at(
            s, Mmin_done, reasons, levels, trail, tags, anz_wl)
     */
    /*@ Given max_lits tot_lits */
    /* Same lift as at the tag-clearing block: the six semantic facts are
       restated at the LHS's own model `Mmin_done'.  The isolated goal
       otherwise had no hypothesis mentioning `M', `F', `A_arr', `K', `focus',
       `words_uip', `kept_done', ... or the locals `i'/`j', so every RHS
       conjunct about the fresh `Mstats_upd' was refutable.  Restating
       `analyze_minimize_loop_inv' is also what pins `i' and `j'. */
    /*@ analysis_core_equiv(M, Mmin_done) &&
          msolver_seed_shadow(Mmin_done) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mmin_done, anz_focus) &&
          analysis_tags_exact(anz_n, ms_tags(Mmin_done), ms_tagged(Mmin_done)) &&
          analyze_clause_cert(anz_n, anz_F, Mmin_done, words_uip) &&
          analyze_minimize_loop_inv(
            anz_n, Mmin_done, words_uip, kept_done, removed_done,
            words_done, T_done, i, j) &&
          store(&(s->stats.max_literals), max_lits) *
          store(&(s->stats.tot_literals), tot_lits) *
          solver_literal_stats_frame_at(
            s, Mmin_done, reasons, levels, trail, tags, anz_wl)
        which implies exists (Mstats_upd : msolver),
          analysis_core_equiv(M, Mstats_upd) &&
          msolver_seed_shadow(Mstats_upd) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats_upd, anz_focus) &&
          analysis_tags_exact(anz_n, ms_tags(Mstats_upd), ms_tagged(Mstats_upd)) &&
          analyze_clause_cert(anz_n, anz_F, Mstats_upd, words_uip) &&
          analyze_minimize_loop_inv(
            anz_n, Mstats_upd, words_uip, kept_done, removed_done,
            words_done, T_done, i, j) &&
          solver_rep_analyze_at(
            s, Mstats_upd, reasons, levels, trail, tags, anz_wl)
     */

    /*@ exists (Mstats : msolver) (words_compact : list Z),
          analysis_core_equiv(M, Mstats) &&
          msolver_seed_shadow(Mstats) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats, anz_focus) &&
          words_compact == sublist(0, j, words_done) &&
          1 <= Zlength(words_compact) && Zlength(words_compact) <= anz_n &&
          Forall(lit_wf_c(anz_n), words_compact) &&
          NoDup(map(lit_var_c, words_compact)) &&
          analyze_clause_cert(anz_n, anz_F, Mstats, words_compact) &&
          analysis_tags_exact(anz_n, ms_tags(Mstats), ms_tagged(Mstats)) &&
          solver_rep_analyze_at(
            s, Mstats, reasons, levels, trail, tags, anz_wl) *
          veci_rep_at(learnt, lits, words_compact, cap_done)
     */
    /*@ Given Mstats words_compact */

    // clear tags
    /* The unfold has to precede the call: veci_begin needs the tagged vector
       exposed, and it is buried inside the opaque solver_rep_analyze_at, which
       no strategy rule can open.  The backing pointer is bound as an
       existential because `tagged` is what the call is about to assign.  The
       vector's own bounds are re-emitted -- veci_rep_at carries them as a pure
       conjunct, and veci_begin's Require needs them. */
    /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats, anz_focus) &&
        solver_rep_analyze_at(
          s, Mstats, reasons, levels, trail, tags, anz_wl)
        which implies exists tagged_ptr,
          0 <= Zlength(ms_tagged(Mstats)) &&
          Zlength(ms_tagged(Mstats)) <= ms_tagged_cap(Mstats) &&
          0 < ms_tagged_cap(Mstats) &&
          ms_tagged_cap(Mstats) <= INT_MAX &&
          store(&(s->tags), tags) *
          CharArray::seg(tags, 0, anz_n, ms_tags(Mstats)) *
          CharArray::undef_seg(tags, anz_n, ms_cap(Mstats)) *
          veci_rep_at(&(s->tagged), tagged_ptr, ms_tagged(Mstats),
                      ms_tagged_cap(Mstats)) *
          solver_tags_tagged_frame_at(
            s, Mstats, reasons, levels, trail, anz_wl)
     */
    tagged = veci_begin(&s->tagged);
    /*@ Inv Assert exists (tags_now : list Z),
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          analyze_clear_loop_inv(
            anz_n, i, ms_tagged(Mstats), ms_tags(Mstats), tags_now) &&
          0 <= i && i <= Zlength(ms_tagged(Mstats)) &&
          (i == Zlength(ms_tagged(Mstats)) ||
           (i < Zlength(ms_tagged(Mstats)) &&
            0 <= ms_tagged(Mstats)[i] &&
            ms_tagged(Mstats)[i] < anz_n)) &&
          analysis_core_equiv(M, Mstats) &&
          msolver_seed_shadow(Mstats) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats, anz_focus) &&
          analyze_clause_cert(anz_n, anz_F, Mstats, words_compact) &&
          1 <= Zlength(words_compact) && Zlength(words_compact) <= anz_n &&
          Forall(lit_wf_c(anz_n), words_compact) &&
          store(&(s->tags), tags) *
          CharArray::seg(tags, 0, anz_n, tags_now) *
          CharArray::undef_seg(tags, anz_n, ms_cap(Mstats)) *
          veci_rep_at(&(s->tagged), tagged, ms_tagged(Mstats),
                      ms_tagged_cap(Mstats)) *
          solver_tags_tagged_frame_at(
            s, Mstats, reasons, levels, trail, anz_wl) *
          veci_rep_at(learnt, lits, words_compact, cap_done) *
          has_permission(&c) * has_permission(&cnt) *
          has_permission(&p) * has_permission(&ind) *
          has_permission(&j) * has_permission(&minl)
     */
    for (i = 0; i < veci_size(&s->tagged); i++)
        /*@ Given tags_now */
        /*@ 0 <= ms_tagged(Mstats)[i - 0] &&
              ms_tagged(Mstats)[i - 0] < anz_n &&
              CharArray::seg(tags, 0, anz_n, tags_now)
            which implies exists old_tag,
              store(pointer_offset(
                      tags, ms_tagged(Mstats)[i - 0],
                      sizeof(char), char), char, old_tag) *
              CharArray::missing_i(
                tags, ms_tagged(Mstats)[i - 0], 0, anz_n, tags_now)
         */
        tags[tagged[i]] = MINISAT_QCP_ZERO_VALUE;
    /*@ Given tags_now */
    veci_resize(&s->tagged,0);

    /* Name the loop's output list and the resized vector by matching, then
       introduce the cleared ghost on a which-implies RHS.  Stating
       `ms_tags(Mclear) == repeat_Z(0, n)` in an ordinary exists-led assertion
       would unify Mclear against the *old* ghost and silently assert a false
       equation. */
    /*@ exists (tags_final tagged_list : list Z) tagged_p tagged_cap_final,
          tags_final == tags_now &&
          tagged_list == sublist(0, 0, ms_tagged(Mstats)) &&
          Zlength(tagged_list) == 0 &&
          analysis_tags_exact(anz_n, tags_final, tagged_list) &&
          store(&(s->tags), tags) *
          CharArray::seg(tags, 0, anz_n, tags_final) *
          CharArray::undef_seg(tags, anz_n, ms_cap(Mstats)) *
          veci_rep_at(&(s->tagged), tagged_p, tagged_list, tagged_cap_final) *
          solver_tags_tagged_frame_at(
            s, Mstats, reasons, levels, trail, anz_wl)
     */
    /*@ Given tags_final tagged_list tagged_p tagged_cap_final */
    /* The three semantic facts are restated at the LHS's OWN model `Mstats';
       the RHS states them at the fresh `Mclear', which the block itself relates
       to `Mstats'.  Without them `M', `F', `A_arr', `K', `focus' and
       `words_compact' were free universals in the isolated goal (its PreH list
       was EMPTY) and `analysis_core_equiv M Mclear' was refutable. */
    /*@ analysis_core_equiv(M, Mstats) &&
          msolver_seed_shadow(Mstats) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats, anz_focus) &&
          analyze_clause_cert(anz_n, anz_F, Mstats, words_compact) &&
          Zlength(tagged_list) == 0 &&
          analysis_tags_exact(anz_n, tags_final, tagged_list) &&
          store(&(s->tags), tags) *
          CharArray::seg(tags, 0, anz_n, tags_final) *
          CharArray::undef_seg(tags, anz_n, ms_cap(Mstats)) *
          veci_rep_at(&(s->tagged), tagged_p, tagged_list, tagged_cap_final) *
          solver_tags_tagged_frame_at(
            s, Mstats, reasons, levels, trail, anz_wl)
        which implies exists (Mclear : msolver),
          analysis_core_equiv(M, Mclear) &&
          msolver_seed_shadow(Mclear) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mclear, anz_focus) &&
          ms_tags(Mclear) == repeat_Z(0, anz_n) &&
          ms_tagged(Mclear) == nil &&
          analyze_clause_cert(anz_n, anz_F, Mclear, words_compact) &&
          solver_rep_analyze_at(
            s, Mclear, reasons, levels, trail, tags, anz_wl)
     */
    /*@ Given Mclear */

#ifdef DEBUG
    for (i = 0; i < s->size; i++)
        assert(tags[i] == MINISAT_QCP_ZERO_VALUE);
#endif

#ifdef VERBOSEDEBUG
    printf(L_IND"Learnt {", L_ind);
    for (i = 0; i < veci_size(learnt); i++) printf(" "L_LIT, L_lit(lits[i]));
#endif
    if (veci_size(learnt) > 1){
        /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mclear, anz_focus) &&
            solver_rep_analyze_at(
              s, Mclear, reasons, levels, trail, tags, anz_wl)
            which implies
              solver_shape(Mclear) &&
              store(&(s->reasons), reasons) *
              PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mclear)) *
              PtrArray::undef_seg(reasons, anz_n, ms_cap(Mclear)) *
              store(&(s->levels), levels) *
              IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mclear))) *
              IntArray::undef_seg(levels, anz_n, ms_cap(Mclear)) *
              solver_reason_levels_frame_at(s, Mclear, trail, tags, anz_wl)
         */
        int max_i = 1;
        /*@ Forall(lit_wf_c(anz_n), words_compact) &&
              1 < Zlength(words_compact)
            which implies
              Forall(lit_wf_c(anz_n), words_compact) &&
              1 < Zlength(words_compact) &&
              0 <= lit_var_c(words_compact[1 - 0]) &&
              lit_var_c(words_compact[1 - 0]) < anz_n
         */
        int max   = levels[lit_var(lits[1])];
        lit tmp;

        /*@ Inv Assert
              s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
              analyze_max_loop_inv(anz_n, Mclear, words_compact,
                                   i, max_i, max) &&
              2 <= i && i <= Zlength(words_compact) &&
              1 <= max_i && max_i < i &&
              Forall(lit_wf_c(anz_n), words_compact) &&
              analysis_core_equiv(M, Mclear) &&
              msolver_seed_shadow(Mclear) &&
              analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mclear, anz_focus) &&
              ms_tags(Mclear) == repeat_Z(0, anz_n) &&
              ms_tagged(Mclear) == nil &&
              analyze_clause_cert(anz_n, anz_F, Mclear, words_compact) &&
              store(&(s->reasons), reasons) *
              PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mclear)) *
              PtrArray::undef_seg(reasons, anz_n, ms_cap(Mclear)) *
              store(&(s->levels), levels) *
              IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mclear))) *
              IntArray::undef_seg(levels, anz_n, ms_cap(Mclear)) *
              solver_reason_levels_frame_at(s, Mclear, trail, tags, anz_wl) *
              veci_rep_at(learnt, lits, words_compact, cap_done) *
              has_permission(&c) * has_permission(&cnt) *
              has_permission(&p) * has_permission(&ind) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged) * has_permission(&tmp)
         */
        for (i = 2; i < veci_size(learnt); i++)
            /*@ Forall(lit_wf_c(anz_n), words_compact) &&
                  0 <= i && i < Zlength(words_compact)
                which implies
                  Forall(lit_wf_c(anz_n), words_compact) &&
                  0 <= i && i < Zlength(words_compact) &&
                  0 <= lit_var_c(words_compact[i - 0]) &&
                  lit_var_c(words_compact[i - 0]) < anz_n
             */
            if (levels[lit_var(lits[i])] > max){
                max   = levels[lit_var(lits[i])];
                max_i = i;
            }

        tmp         = lits[1];
        lits[1]     = lits[max_i];
        lits[max_i] = tmp;
        /* The two element writes leave the learnt array as IntArray::full
           (int_array rule 2 refolds missing_i to `full`).  veci_rep_at is
           defined over IntArray::seg, and int_array rule 13 only converts
           seg -> full, never the reverse -- so convert it here, inside the arm,
           and bind the swapped list rather than spelling it. */
        /*@ exists (words_sw : list Z) len_sw cap_sw,
              0 < cap_sw &&
              words_sw == replace_Znth(
                max_i, Znth(1, words_compact, 0),
                replace_Znth(
                  1, Znth(max_i, words_compact, 0), words_compact)) &&
              store(&(learnt->size), len_sw) *
              store(&(learnt->cap), cap_sw) *
              store(&(learnt->ptr), lits) *
              IntArray::full(lits, len_sw, words_sw) *
              IntArray::undef_seg(lits, len_sw, cap_sw)
         */
        /*@ Given words_sw len_sw cap_sw */
        /*@ 0 < cap_sw &&
              store(&(learnt->size), len_sw) *
              store(&(learnt->cap), cap_sw) *
              store(&(learnt->ptr), lits) *
              IntArray::full(lits, len_sw, words_sw) *
              IntArray::undef_seg(lits, len_sw, cap_sw)
            which implies
              len_sw == Zlength(words_sw) &&
              veci_rep_at(learnt, lits, words_sw, cap_sw)
         */
        /* Refold before the arm ends: the other arm of this `if` never
           unfolded, and two arms can only be joined at a common shape. */
        /*@ solver_shape(Mclear) &&
              store(&(s->reasons), reasons) *
              PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mclear)) *
              PtrArray::undef_seg(reasons, anz_n, ms_cap(Mclear)) *
              store(&(s->levels), levels) *
              IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mclear))) *
              IntArray::undef_seg(levels, anz_n, ms_cap(Mclear)) *
              solver_reason_levels_frame_at(s, Mclear, trail, tags, anz_wl)
            which implies
              solver_rep_analyze_at(
                s, Mclear, reasons, levels, trail, tags, anz_wl)
         */
    }
#ifdef VERBOSEDEBUG
    {
        int lev = veci_size(learnt) > 1 ? levels[lit_var(lits[1])] : 0;
        printf(" } at level %d\n", lev);
    }
#endif
    /*@ exists (Mfinal : msolver) (words_final : list Z)
                      cap_final blevel,
          analysis_core_equiv(M, Mfinal) &&
          msolver_seed_shadow(Mfinal) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mfinal, anz_focus) &&
          1 <= Zlength(words_final) && Zlength(words_final) <= anz_n &&
          Forall(lit_wf_c(anz_n), words_final) &&
          NoDup(map(lit_var_c, words_final)) &&
          analyze_clause_cert(anz_n, anz_F, Mfinal, words_final) &&
          analyze_backjump_cert(anz_n, Mfinal, words_final, blevel) &&
          ms_tags(Mfinal) == repeat_Z(0, anz_n) &&
          ms_tagged(Mfinal) == nil &&
          solver_rep_analyze_at(
            s, Mfinal, reasons, levels, trail, tags, anz_wl) *
          veci_rep_at(learnt, lits, words_final, cap_final)
     */
    /*@ Given Mfinal */
    /*@ solver_rep_analyze_at(
          s, Mfinal, reasons, levels, trail, tags, anz_wl)
        which implies solver_rep_levels_wl_at(s, Mfinal, anz_wl, levels) *
          has_permission(&reasons) * has_permission(&trail) *
          has_permission(&tags) */
    /*@ Assert s == s@pre && learnt == learnt@pre &&
          solver_analyze_post(
          s, learnt, levels_ptr, anz_n, anz_F, anz_A_arr, K, M, anz_focus, anz_wl) *
          has_permission(&c) * has_permission(&trail) *
          has_permission(&tags) * has_permission(&reasons) *
          has_permission(&levels) * has_permission(&cnt) *
          has_permission(&p) * has_permission(&ind) *
          has_permission(&lits) * has_permission(&i) *
          has_permission(&j) * has_permission(&minl) *
          has_permission(&tagged) */
}


/* Boolean constraint propagation to a fixed point over the watcher lists.
   Assigns every literal forced by a clause that has become unit, repairing the
   watches as it goes, and stops at the first clause false under the
   assignment.  Returns 1 when propagation is quiescent, 0 with the conflicting
   clause in `conflict_out`, or -2 when a watcher list cannot grow. */
int solver_propagate(solver* s, clause **conflict_out)

/*@ With (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M0 : msolver)
         assigns_entry levels_entry wlists_entry
    Require solver_propagate_pre(
              s, conflict_out, n, F, A_arr, K, M0,
              assigns_entry, levels_entry, wlists_entry)
    Ensure solver_propagate_post(
             s, conflict_out, n, F, A_arr, K, M0,
             assigns_entry, levels_entry, __return, wlists_entry)
 */
{
    /*@ solver_propagate_pre(
          s, conflict_out, n, F, A_arr, K, M0,
          assigns_entry, levels_entry, wlists_entry)
        which implies
        exists rsn trl,
          solver_shape(M0) &&
          solver_propagation_inv(n, F, A_arr, K, M0) &&
          msolver_seed_shadow(M0) &&
          0 <= mt_qhead(ms_core(M0)) &&
          mt_qhead(ms_core(M0)) <= ms_qtail(M0) &&
          ms_qtail(M0) <= ms_size(M0) &&
          ms_size(M0) <= ms_cap(M0) &&
          Zlength(mt_trail(ms_core(M0))) == ms_qtail(M0) &&
          solver_propagate_open_at(s, M0, wlists_entry, assigns_entry, rsn,
                                   levels_entry, trl) *
          clause_db_rep(ms_prob(M0)) *
          clause_db_rep(ms_learnt(M0)) *
          solver_binary_rep(M0) *
          undef_data_at(conflict_out, clause *)
     */
    lbool*  values = s->assigns;
    clause* confl  = (clause*)0;
    lit*    lits;

    *conflict_out = (clause *)0;

    //printf("solver_propagate\n");
    /*@ Inv Assert exists M rsn trl cf,
          s == s@pre && conflict_out == conflict_out@pre &&
          values == assigns_entry &&
          solver_shape(M) &&
          solver_propagation_loop_inv(n, F, A_arr, K, M0, M, cf) &&
          minisat_propagation_reuse_loop(n, M0, M, cf) &&
          msolver_seed_shadow(M) &&
          0 <= mt_qhead(ms_core(M)) &&
          mt_qhead(ms_core(M)) <= ms_qtail(M) &&
          ms_qtail(M) <= ms_size(M) &&
          ms_size(M) <= ms_cap(M) &&
          Zlength(mt_trail(ms_core(M))) == ms_qtail(M) &&
          solver_propagate_open_at(s, M, wlists_entry, values, rsn,
                                   levels_entry, trl) *
          clause_db_rep(ms_prob(M)) *
          clause_db_rep(ms_learnt(M)) *
          solver_binary_rep(M) *
          data_at(conflict_out, 0) *
          store(&(confl), clause *, cf) *
          has_permission(&(lits))
     */
    while (confl == 0 && s->qtail - s->qhead > 0){
        /*@ Given M rsn trl cf */
        /*@ cf == 0 &&
              solver_propagation_loop_inv(n, F, A_arr, K, M0, M, cf) &&
              minisat_propagation_reuse_loop(n, M0, M, cf)
            which implies
            solver_propagation_inv(n, F, A_arr, K, M) &&
            propagation_caller_frame(M0, M)
         */
        lit  p  = s->trail[s->qhead];
        s->qhead++;
        /* solver_read_wlist wants the field folded (solver_wlists_handle is
           exactly that one store, defined in solver_qcp_lib.v); this is the
           inverse of the fold/unfold idiom this loop repeats at every
           `solver_read_wlist` call.  The literal bound has to be derived
           explicitly: solver_propagation_inv is an opaque Coq Prop, so QCP
           gets nothing from it on its own. */
        /*@ solver_propagation_inv(n, F, A_arr, K, M) &&
              p == Znth(mt_qhead(ms_core(M)), mt_trail(ms_core(M)), 0) &&
              0 <= mt_qhead(ms_core(M)) &&
              mt_qhead(ms_core(M)) < ms_qtail(M) &&
              store(&(s->wlists), vecp *, wlists_entry)
            which implies
              solver_propagation_inv(n, F, A_arr, K, M) &&
              p == Znth(mt_qhead(ms_core(M)), mt_trail(ms_core(M)), 0) &&
              0 <= p && p < 2 * n &&
              solver_wlists_handle(s, wlists_entry)
         */
        vecp* ws = solver_read_wlist(s,p) /*@ where rdw_wl = wlists_entry */;
        /* ... and unfold it straight back, the same fold/unfold idiom repeated above. */
        /*@ solver_wlists_handle(s, wlists_entry)
            which implies store(&(s->wlists), vecp *, wlists_entry) */
        /* Open the watcher slot the call just returned. */
        /*@ 0 <= p && p < 2 * n &&
              n == ms_size(M) &&
              ws == vecp_slot(wlists_entry, p) &&
              wlists_rep(wlists_entry, ms_size(M), ms_wm(M), ms_wcaps(M))
            which implies
              0 <= p && p < 2 * n &&
              n == ms_size(M) &&
              ws == vecp_slot(wlists_entry, p) &&
              wlists_focus_at(wlists_entry, p, ms_wm(M), ms_wcaps(M), ws)
         */
        /*@ store(&(s->wlists), vecp *, wlists_entry) *
              wlists_focus_at(wlists_entry, p, ms_wm(M), ms_wcaps(M), ws)
            which implies
            exists wm_pre words wm_post caps_pre wcap caps_post,
              ms_wm(M) == app(wm_pre, cons(words, wm_post)) &&
              ms_wcaps(M) == app(caps_pre, cons(wcap, caps_post)) &&
              Zlength(wm_pre) == p && Zlength(caps_pre) == p &&
              ws == vecp_slot(wlists_entry, p) &&
              wlists_source_hole_handle(
                s, wlists_entry, Zlength(wm_pre),
                wm_pre, wm_post, caps_pre, caps_post) *
              vecp_rep(ws, words, wcap)
         */
        /*@ Given wm_pre words wm_post caps_pre wcap */
        clause **begin = (clause**)vecp_begin(ws);
        clause **endvar   = begin + vecp_size(ws);
        clause **i, **j;

        /*@ exists words0 wcap0,
              words0 == words && wcap0 == wcap &&
              endvar == begin + Zlength(words0) &&
              vecp_rep_at(ws, begin, words0, wcap0)
            which implies
              endvar == begin + Zlength(words) &&
              0 <= Zlength(words) && Zlength(words) <= wcap &&
              0 < wcap && wcap <= INT_MAX &&
              store(&(ws->size), int, Zlength(words)) *
              store(&(ws->cap), int, wcap) *
              store(&(ws->ptr), void **, begin) *
              PtrArray::seg(begin, 0, Zlength(words), words) *
              PtrArray::undef_seg(begin, Zlength(words), wcap)
         */
        s->stats.propagations++;
        s->simpdb_props = minisat_simpdb_props_after_propagation(s->simpdb_props);

        //printf("checking lit %d: "L_LIT"\n", veci_size(ws), L_lit(p));
        /*@ solver_shape(M)
            which implies
            exists Mentry source_words,
              Mentry == M && source_words == words && solver_shape(M)
         */
        j = begin;
        /* This loop is spelled as `i = begin; while (i < endvar) { ... }' rather
           than `for (i = begin; i < endvar; )' because symexec SIGSEGVs on a
           for-loop whose UPDATE clause is omitted and which actually iterates
           (an omitted CONDITION always crashes; an omitted UPDATE crashes only
           when the body does not break before the back edge; an omitted init
           alone is safe).  `init; while (cond) body' is the C-standard expansion
           of `for (init; cond; ) body' (C11 6.8.5.3p1), so this is a
           transcription of the frozen upstream loop, not a behaviour change.
           `i = begin;' sits above the invariant because the invariant
           constrains `i' (`i == begin + ii', with `ii == 0' on entry). */
        i = begin;
        /*@ Inv Assert exists Mscan watch_memory logical_words,
              exists scan_wm_pre scan_wm_post scan_caps_pre scan_caps_post,
              exists scan_wcap retained moved rest garbage,
              exists ii jj prop_count simp_count,
              exists rsn_scan trl_scan Mentry source_words,
              s == s@pre && conflict_out == conflict_out@pre &&
          values == assigns_entry &&
              solver_shape(Mscan) &&
              msolver_seed_shadow(Mscan) &&
              propagation_caller_frame(M0, Mscan) &&
              propagation_scan_frontier(Mentry, Mscan, p) &&
              solver_propagation_scan_semantics(
                n, F, A_arr, K, Mscan, p, confl, retained, rest) &&
              minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
              propagation_watch_scan_physical(
                source_words, retained, moved, rest, garbage,
                watch_memory, ii, jj) &&
              logical_words == app(retained, rest) &&
              ms_wm(Mscan) ==
                app(scan_wm_pre, cons(logical_words, scan_wm_post)) &&
              ms_wcaps(Mscan) ==
                app(scan_caps_pre, cons(scan_wcap, scan_caps_post)) &&
              Zlength(scan_wm_pre) == p &&
              Zlength(scan_caps_pre) == p &&
              ws == vecp_slot(wlists_entry, p) &&
              endvar == begin + Zlength(source_words) &&
              Zlength(watch_memory) == Zlength(source_words) &&
              i == begin + ii && j == begin + jj &&
              0 <= jj && jj <= ii &&
              0 <= ii && ii <= Zlength(source_words) &&
              (ii != 0 ||
               Mscan == msolver_propagation_scan_begin(
                      Mentry, simp_count, prop_count)) &&
              simp_count == ms_simpdb_props(Mscan) &&
              prop_count == stats_propagations(ms_stats(Mscan)) &&
              0 <= Zlength(source_words) &&
              Zlength(source_words) <= scan_wcap &&
              0 < scan_wcap && scan_wcap <= INT_MAX &&
              store(&(ws->size), int, Zlength(source_words)) *
              store(&(ws->cap), int, scan_wcap) *
              store(&(ws->ptr), void **, begin) *
              PtrArray::full(
                begin, Zlength(source_words), watch_memory) *
              PtrArray::undef_seg(
                begin, Zlength(source_words), scan_wcap) *
              wlists_source_hole_handle(
                s, wlists_entry, Zlength(scan_wm_pre),
                scan_wm_pre, scan_wm_post, scan_caps_pre, scan_caps_post) *
              clause_db_rep(ms_prob(Mscan)) *
              clause_db_rep(ms_learnt(Mscan)) *
              CharArray::seg(
                values, 0, ms_size(Mscan),
                mt_assigns(ms_core(Mscan))) *
              CharArray::undef_seg(
                values, ms_size(Mscan), ms_cap(Mscan)) *
              store(&(s->reasons), clause **, rsn_scan) *
              store(&(s->levels), int *, levels_entry) *
              store(&(s->trail), lit *, trl_scan) *
              PtrArray::seg(
                rsn_scan, 0, ms_size(Mscan),
                ms_reason_words(Mscan)) *
              PtrArray::undef_seg(
                rsn_scan, ms_size(Mscan), ms_cap(Mscan)) *
              IntArray::seg(
                levels_entry, 0, ms_size(Mscan),
                mt_levels(ms_core(Mscan))) *
              IntArray::undef_seg(
                levels_entry, ms_size(Mscan), ms_cap(Mscan)) *
              IntArray::seg(
                trl_scan, 0, ms_qtail(Mscan),
                mt_trail(ms_core(Mscan))) *
              IntArray::undef_seg(
                trl_scan, ms_qtail(Mscan), ms_cap(Mscan)) *
              veci_rep(
                &(s->trail_lim), mt_lim(ms_core(Mscan)),
                ms_lim_cap(Mscan)) *
              store(&(s->qhead), int,
                    mt_qhead(ms_core(Mscan))) *
              store(&(s->qtail), int, ms_qtail(Mscan)) *
              store(&(s->simpdb_props), int, simp_count) *
              store(&(s->assigns), lbool *, values) *
              store(&(s->binary), clause *, ms_binary(Mscan)) *
              solver_binary_rep(Mscan) *
              store(&(s->stats.propagations),
                    unsigned long long, prop_count) *
              store(&(s->stats.inspects), unsigned long long,
                    stats_inspects(ms_stats(Mscan))) *
              solver_propagate_frame(s, Mscan) *
              data_at(conflict_out, 0) *
              has_permission(&(lits))
        */
        while (i < endvar) {
            /*@ Given Mscan watch_memory logical_words scan_wm_pre scan_wm_post scan_caps_pre
                      scan_caps_post scan_wcap retained moved rest garbage ii jj prop_count
                      simp_count rsn_scan trl_scan Mentry source_words */
            /*@ endvar == begin + Zlength(source_words) &&
                  i == begin + ii && j == begin + jj &&
                  0 <= jj && jj <= ii &&
                  0 <= ii && ii < Zlength(source_words) &&
                  i < endvar &&
                  PtrArray::full(
                    begin, Zlength(source_words), watch_memory)
                which implies
                exists raw_prefix scan_current raw_suffix,
              endvar == begin + Zlength(source_words) &&
                  i == begin + ii && j == begin + jj &&
                  0 <= jj && jj <= ii && 0 <= ii &&
                  ii < Zlength(source_words) &&
                  0 <= scan_current &&
                  watch_memory ==
                    app(raw_prefix, cons(scan_current, raw_suffix)) &&
                  Zlength(raw_prefix) == ii &&
                  ((jj == ii &&
                    i == begin + ii &&
                    j == begin + jj &&
                    j == i &&
                    propagation_ptr_segment(
                      begin, 0, ii, raw_prefix) *
                    data_at(
                      begin + ii * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, ii + 1,
                      Zlength(source_words), raw_suffix)) ||
                   (jj < ii &&
                    i == begin + ii &&
                    j == begin + jj &&
                    propagation_ptr_segment(
                      begin, 0, jj,
                      sublist(0, jj, raw_prefix)) *
                    data_at(
                      begin + jj * sizeof(struct clause_t *),
                      struct clause_t *, Znth(jj, raw_prefix, 0)) *
                    propagation_ptr_segment(
                      begin, jj + 1, ii,
                      sublist(jj + 1, ii, raw_prefix)) *
                    data_at(
                      begin + ii * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, ii + 1,
                      Zlength(source_words), raw_suffix)))
                  $ scan_move scan_same
            */
            /*@ Given raw_prefix scan_current raw_suffix */
            if (clause_is_lit(*i)){
                *j = *i;
                /*@ app(raw_prefix,
                      cons(scan_current, raw_suffix)) == watch_memory &&
                    Zlength(raw_prefix) == ii &&
                    ii <= jj && jj <= ii &&
                    propagation_ptr_segment(
                      begin, 0, ii, raw_prefix) *
                    data_at(
                      begin + ii * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, ii + 1,
                      Zlength(source_words), raw_suffix)
                    $ scan_same
                    which implies
                    PtrArray::full(
                      begin, Zlength(source_words),
                      replace_Znth(
                        jj, scan_current, watch_memory))
                    $ scan_same
                 */
                /*@ app(raw_prefix,
                      cons(scan_current, raw_suffix)) == watch_memory &&
                    Zlength(raw_prefix) == ii &&
                    0 <= jj && jj < ii &&
                    propagation_ptr_segment(
                      begin, 0, jj,
                      sublist(0, jj, raw_prefix)) *
                    data_at(
                      begin + jj * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, jj + 1, ii,
                      sublist(jj + 1, ii, raw_prefix)) *
                    data_at(
                      begin + ii * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, ii + 1,
                      Zlength(source_words), raw_suffix)
                    $ scan_move
                    which implies
                    PtrArray::full(
                      begin, Zlength(source_words),
                      replace_Znth(
                        jj, scan_current, watch_memory))
                    $ scan_move
                 */
                /*@ PtrArray::full(
                      begin, Zlength(source_words),
                      replace_Znth(
                        jj, scan_current, watch_memory))
                    which implies
                    exists tagged_memory,
                      tagged_memory ==
                        replace_Znth(
                          jj, scan_current, watch_memory) &&
                      PtrArray::full(
                        begin, Zlength(source_words),
                        tagged_memory)
                 */
                /*@ Given tagged_memory */
                j++;
                /*@ i == begin + ii &&
                      0 <= ii &&
                      ii < Zlength(source_words) &&
                      Znth(ii, tagged_memory, 0) == scan_current &&
                      PtrArray::full(
                        begin, Zlength(source_words),
                        tagged_memory)
                    which implies
                    Znth(ii, tagged_memory, 0) ==
                      scan_current &&
                    data_at(i, Znth(ii, tagged_memory, 0)) *
                    PtrArray::missing_i(
                      begin, ii, 0, Zlength(source_words),
                      tagged_memory)
                 */
                /*@ exists rsn trl,
                    enqueue_input(ms_size(Mscan), tag_lit(scan_current),
                                  ms_qtail(Mscan), mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)), ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan))) &&
                    0 <= ms_size(Mscan) &&
                    ms_size(Mscan) <= ms_cap(Mscan) &&
                    ms_cap(Mscan) <= INT_MAX &&
                    ms_qtail(Mscan) <= ms_cap(Mscan) &&
                    data_at(i, Znth(ii, tagged_memory, 0)) *
                    store(&(s->qtail), int, ms_qtail(Mscan)) *
                    store(&(s->assigns), lbool *, values) *
                    store(&(s->levels), int *, levels_entry) *
                    store(&(s->reasons), clause **, rsn) *
                    store(&(s->trail), lit *, trl) *
                    CharArray::seg(values, 0, ms_size(Mscan),
                                   mt_assigns(ms_core(Mscan))) *
                    CharArray::undef_seg(values, ms_size(Mscan), ms_cap(Mscan)) *
                    IntArray::seg(levels_entry, 0, ms_size(Mscan),
                                  mt_levels(ms_core(Mscan))) *
                    IntArray::undef_seg(levels_entry, ms_size(Mscan),
                                        ms_cap(Mscan)) *
                    PtrArray::seg(rsn, 0, ms_size(Mscan),
                                  ms_reason_words(Mscan)) *
                    PtrArray::undef_seg(rsn, ms_size(Mscan), ms_cap(Mscan)) *
                    IntArray::seg(trl, 0, ms_qtail(Mscan),
                                  mt_trail(ms_core(Mscan))) *
                    IntArray::undef_seg(trl, ms_qtail(Mscan), ms_cap(Mscan)) *
                    veci_rep(&(s->trail_lim), mt_lim(ms_core(Mscan)),
                             ms_lim_cap(Mscan))
                    which implies
                    enqueue_input(ms_size(Mscan), tag_lit(scan_current),
                                  ms_qtail(Mscan), mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)), ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan))) &&
                    data_at(i, Znth(ii, tagged_memory, 0)) *
                    enqueue_state_at(s, values, levels_entry,
                                  ms_size(Mscan), ms_cap(Mscan), ms_qtail(Mscan),
                                  mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)), ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan)), mt_lim(ms_core(Mscan)),
                                  ms_lim_cap(Mscan))
                 */
                if (!enqueue(s,clause_read_lit(*i),clause_from_lit(p))){
                    // This LHS names `i` as an address, which is a value mention and so
                    // consumes `&i`.  The RHS must NOT hand the cell back with
                    // `store(&i, clause **, i)`: a self-store mints a FRESH unconstrained
                    // binder for the contents, i.e. it havocs `i`.  A pure mention of `i`
                    // on the RHS returns the cell carrying the LHS's own binder.  The
                    // bound below is written as an
                    // antisymmetric pair rather than `i == begin + ii` on purpose -- a
                    // defining equation is solved before the spatial match and would
                    // re-spell `i` inside this block's own `data_at(i, ...)`.
                    /*@ begin + ii <= i && i <= begin + ii &&
                          data_at(
                          i, Znth(ii, tagged_memory, 0)) *
                          PtrArray::missing_i(
                            begin, ii, 0, Zlength(source_words),
                            tagged_memory)
                        which implies
                        exists tagged_enqueue_conflict_memory,
                          tagged_enqueue_conflict_memory ==
                            replace_Znth(
                              ii,
                              Znth(ii, tagged_memory, 0),
                              tagged_memory) &&
                          begin + ii <= i && i <= begin + ii &&
                          PtrArray::full(
                            begin, Zlength(source_words),
                            tagged_enqueue_conflict_memory)
                     */
                    /*@ Given tagged_enqueue_conflict_memory */
                    confl = s->binary;
                    /*@ exists confl0,
                          confl == confl0 && confl0 == ms_binary(Mscan) &&
                          solver_binary_rep(Mscan) && solver_shape(Mscan)
                        which implies
                        exists confl0,
                          confl == confl0 && confl0 == ms_binary(Mscan) &&
                          Zlength(ms_binary_lits(Mscan)) == 2 &&
                          solver_shape(Mscan) &&
                          store(&(confl->size_learnt), int, 4) *
                          undef_data_at(&(confl->activity), float) *
                          IntArray::seg(clause_lits_addr(confl), 0, 2,
                                        ms_binary_lits(Mscan))
                     */
                    (clause_begin(confl))[1] =
                      lit_neg(p) /*@ where (original) */;
                    /*@ Assert exists scratch_contents scratch_base0,
                          s == s@pre && conflict_out == conflict_out@pre &&
                          values == assigns_entry &&
                          solver_shape(Mscan) &&
                          msolver_seed_shadow(Mscan) &&
                          propagation_caller_frame(M0, Mscan) &&
                          propagation_scan_frontier(Mentry, Mscan, p) &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0,
                            retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          propagation_watch_scan_physical(
                            source_words, retained, moved, rest, garbage,
                            watch_memory, ii, jj) &&
                          rest == cons(scan_current, raw_suffix) &&
                          confl == ms_binary(Mscan) &&
                          clause_lits_pointer(ms_binary(Mscan), scratch_base0) &&
                          Zlength(scratch_contents) == 2 &&
                          Znth(1, scratch_contents, 0) == lit_neg_c(p) &&
                          endvar == begin + Zlength(source_words) &&
                          i == begin + ii && j == begin + jj + 1 &&
                          0 <= jj && jj <= ii && 0 <= ii &&
                          ii < Zlength(source_words) && 0 <= scan_current &&
                          propagation_binary_conflict_scan_ready(
                            n, Mscan, p, scan_current, source_words,
                            scan_wcap, simp_count, prop_count) &&
                          watch_memory ==
                            app(raw_prefix, cons(scan_current, raw_suffix)) &&
                          Zlength(raw_prefix) == ii &&
                          tagged_enqueue_conflict_memory ==
                            replace_Znth(
                              jj, scan_current, watch_memory) &&
                          Znth(ii, tagged_enqueue_conflict_memory, 0) ==
                            scan_current &&
                          logical_words == app(retained, rest) &&
                          ms_wm(Mscan) ==
                            app(scan_wm_pre,
                              cons(logical_words, scan_wm_post)) &&
                          ms_wcaps(Mscan) == app(scan_caps_pre, cons(scan_wcap, scan_caps_post)) &&
                          Zlength(scan_wm_pre) == p && Zlength(scan_caps_pre) == p &&
                          ws == vecp_slot(wlists_entry, p) &&
                          IntArray::full(scratch_base0, 2, scratch_contents) *
                          store(&(confl->size_learnt), int, 4) *
                          undef_data_at(&(confl->activity), float) *
                          enqueue_post_at(s, values, levels_entry,
                                       tag_lit(scan_current), tag_of_lit(p),
                                       ms_size(Mscan), ms_cap(Mscan), ms_qtail(Mscan), 0,
                                       mt_assigns(ms_core(Mscan)),
                                       mt_levels(ms_core(Mscan)),
                                       ms_reason_words(Mscan),
                                       mt_trail(ms_core(Mscan)),
                                       mt_lim(ms_core(Mscan)), ms_lim_cap(Mscan)) *
                          PtrArray::full(
                            begin, Zlength(source_words),
                            tagged_enqueue_conflict_memory) *
                          store(&(ws->size), int, Zlength(source_words)) *
                          store(&(ws->cap), int, scan_wcap) *
                          store(&(ws->ptr), void **, begin) *
                          PtrArray::undef_seg(begin, Zlength(source_words),
                                              scan_wcap) *
                          wlists_source_hole_handle(
                            s, wlists_entry, Zlength(scan_wm_pre),
                            scan_wm_pre, scan_wm_post, scan_caps_pre, scan_caps_post) *
                          undef_data_at(&(lits), lit *) *
                          store(&(s->qhead), int,
                                mt_qhead(ms_core(Mscan))) *
                          store(&(s->simpdb_props), int, simp_count) *
                          store(&(s->binary), clause *, ms_binary(Mscan)) *
                          clause_db_rep(ms_prob(Mscan)) *
                          clause_db_rep(ms_learnt(Mscan)) *
                          store(&(s->stats.propagations), unsigned long long,
                                prop_count) *
                          store(&(s->stats.inspects), unsigned long long,
                                stats_inspects(ms_stats(Mscan))) *
                          solver_propagate_frame(s, Mscan) *
                          data_at(conflict_out, 0)
                    */
                    /*@ Given scratch_contents scratch_base0 */
                    /*@ i == begin + ii &&
                      0 <= ii &&
                      ii < Zlength(source_words) &&
                      Znth(ii, tagged_enqueue_conflict_memory, 0) ==
                        scan_current &&
                      PtrArray::full(
                        begin, Zlength(source_words),
                        tagged_enqueue_conflict_memory)
                        which implies
                        Znth(
                          ii,
                          tagged_enqueue_conflict_memory, 0) ==
                          scan_current &&
                        data_at(
                          i,
                          Znth(
                            ii,
                            tagged_enqueue_conflict_memory, 0)) *
                        PtrArray::missing_i(
                          begin, ii, 0, Zlength(source_words),
                          tagged_enqueue_conflict_memory)
                     */
                    /* clause_lits_pointer is literally `p = clause_lits_addr c`
                       behind a Definition in solver_qcp_lib.v, so QCP cannot see the
                       equality.  Expose it and re-key the segment directly to
                       `clause_lits_addr(confl)`: V2.1.0 no longer chains the
                       opaque address congruence while deriving write permission. */
                    /*@ confl == ms_binary(Mscan) &&
                          clause_lits_pointer(ms_binary(Mscan), scratch_base0) &&
                          IntArray::full(scratch_base0, 2, scratch_contents)
                        which implies
                          confl == ms_binary(Mscan) &&
                          scratch_base0 ==
                            clause_lits_addr(ms_binary(Mscan)) &&
                          scratch_base0 == clause_lits_addr(confl) &&
                          clause_lits_pointer(
                            ms_binary(Mscan), scratch_base0) &&
                          IntArray::seg(
                            clause_lits_addr(confl), 0, 2, scratch_contents)
                     */
                    (clause_begin(confl))[0] = clause_read_lit(*i);
                    /* The `*i` read re-closes the watcher array, so the
                       remainder is PtrArray::full here, not missing_i; no
                       refold block is needed. */
                    i++;

                    // Copy the remaining watches:
                    /*@ Inv Assert exists scratch_base scratch_lits,
                          exists copy_memory copy_src copy_dst,
                          s == s@pre && conflict_out == conflict_out@pre &&
                          values == assigns_entry &&
                          solver_shape(Mscan) &&
                          msolver_seed_shadow(Mscan) &&
                          propagation_caller_frame(M0, Mscan) &&
                          propagation_scan_frontier(Mentry, Mscan, p) &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0,
                            retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          propagation_watch_scan_physical(
                            source_words, retained, moved, rest, garbage,
                            watch_memory, ii, jj) &&
                          rest == cons(scan_current, raw_suffix) &&
                          confl == ms_binary(Mscan) &&
                          clause_lits_pointer(ms_binary(Mscan), scratch_base) &&
                          Zlength(scratch_lits) == 2 &&
                          Znth(0, scratch_lits, 0) == tag_lit(scan_current) &&
                          Znth(1, scratch_lits, 0) == lit_neg_c(p) &&
                          endvar == begin + Zlength(source_words) &&
                          i == begin + copy_src &&
                          j == begin + copy_dst &&
                          0 <= copy_dst && copy_dst <= copy_src &&
                          copy_src <= Zlength(source_words) &&
                          binary_watch_copy_progress(
                            watch_memory, raw_prefix, scan_current,
                            raw_suffix, ii, jj, copy_src, copy_dst,
                            copy_memory) &&
                          logical_words == app(retained, rest) &&
                          ms_wm(Mscan) ==
                            app(scan_wm_pre,
                              cons(logical_words, scan_wm_post)) &&
                          ms_wcaps(Mscan) == app(scan_caps_pre,
                                             cons(scan_wcap, scan_caps_post)) &&
                          Zlength(scan_wm_pre) == p &&
                          Zlength(scan_caps_pre) == p &&
                          ws == vecp_slot(wlists_entry, p) &&
                          propagation_binary_conflict_scan_ready(
                            n, Mscan, p, scan_current, source_words,
                            scan_wcap, simp_count, prop_count) &&
                          IntArray::full(scratch_base, 2, scratch_lits) *
                          store(&(confl->size_learnt), int, 4) *
                          undef_data_at(&(confl->activity), float) *
                          enqueue_post_at(s, values, levels_entry,
                                       tag_lit(scan_current), tag_of_lit(p),
                                       ms_size(Mscan), ms_cap(Mscan), ms_qtail(Mscan), 0,
                                       mt_assigns(ms_core(Mscan)),
                                       mt_levels(ms_core(Mscan)),
                                       ms_reason_words(Mscan),
                                       mt_trail(ms_core(Mscan)),
                                       mt_lim(ms_core(Mscan)), ms_lim_cap(Mscan)) *
                          store(&(ws->size), int, Zlength(source_words)) *
                          store(&(ws->cap), int, scan_wcap) *
                          store(&(ws->ptr), void **, begin) *
                          PtrArray::full(begin, Zlength(source_words),
                                         copy_memory) *
                          PtrArray::undef_seg(begin, Zlength(source_words), scan_wcap) *
                          wlists_source_hole_handle(
                            s, wlists_entry, Zlength(scan_wm_pre),
                            scan_wm_pre, scan_wm_post, scan_caps_pre, scan_caps_post) *
                          undef_data_at(&(lits), lit *) *
                          store(&(s->qhead), int,
                                mt_qhead(ms_core(Mscan))) *
                          store(&(s->simpdb_props), int, simp_count) *
                          store(&(s->binary), clause *, ms_binary(Mscan)) *
                          clause_db_rep(ms_prob(Mscan)) *
                          clause_db_rep(ms_learnt(Mscan)) *
                          store(&(s->stats.propagations), unsigned long long,
                                prop_count) *
                          store(&(s->stats.inspects), unsigned long long,
                                stats_inspects(ms_stats(Mscan))) *
                          solver_propagate_frame(s, Mscan) *
                          data_at(conflict_out, 0)
                     */
                    while (i < endvar) {
                        /*@ Given scratch_base scratch_lits copy_memory copy_src copy_dst */
                        /*@ i == begin + copy_src &&
                              j == begin + copy_dst &&
                              0 <= copy_dst && copy_dst <= copy_src &&
                              copy_src < Zlength(source_words) &&
                              PtrArray::full(begin, Zlength(source_words),
                                             copy_memory)
                            which implies
                            ((copy_dst == copy_src &&
                              i == begin + copy_src &&
                              j == begin + copy_dst &&
                              data_at(
                                i, Znth(copy_src, copy_memory, 0)) *
                              PtrArray::missing_i(begin, copy_src, 0,
                                                  Zlength(source_words),
                                                  copy_memory)) ||
                             (copy_dst < copy_src &&
                              i == begin + copy_src &&
                              j == begin + copy_dst &&
                              PtrArray::seg(begin, 0, copy_dst,
                                            sublist(0, copy_dst,
                                                    copy_memory)) *
                              data_at(
                                j, Znth(copy_dst, copy_memory, 0)) *
                              PtrArray::seg(
                                begin, copy_dst + 1, copy_src,
                                sublist(copy_dst + 1, copy_src,
                                                    copy_memory)) *
                              data_at(
                                i, Znth(copy_src, copy_memory, 0)) *
                              PtrArray::seg(begin, copy_src + 1,
                                            Zlength(source_words),
                                            sublist(copy_src + 1,
                                                    Zlength(source_words),
                                                    copy_memory))))
                         */
                        *j = *i;
                        j++;
                        i++;
                    }
                /*@ Given scratch_base scratch_lits copy_memory copy_src copy_dst */
                /*@ propagation_scan_open(
                      n, F, A_arr, K, M0, Mentry, Mscan, p, 0,
                      source_words, retained, moved, rest, garbage,
                      watch_memory, ii, jj, scan_current, raw_suffix) &&
                    minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                    propagation_binary_conflict_scan_ready(
                      n, Mscan, p, scan_current, source_words,
                      scan_wcap, simp_count, prop_count) &&
                    ms_wm(Mscan) == app(scan_wm_pre,
                      cons(app(retained, rest), scan_wm_post)) && ms_wcaps(Mscan) ==
                      app(scan_caps_pre, cons(scan_wcap, scan_caps_post)) &&
                    Zlength(scan_wm_pre) == p && Zlength(scan_caps_pre) == p && ws == vecp_slot(wlists_entry, p) &&
                    confl <= ms_binary(Mscan) &&
                    ms_binary(Mscan) <= confl &&
                    i >= endvar &&
                    endvar == begin + Zlength(source_words) &&
                    i == begin + copy_src &&
                    j == begin + copy_dst &&
                    0 <= copy_dst &&
                    copy_dst <= copy_src &&
                    copy_src <= Zlength(source_words) &&
                    binary_watch_copy_progress(
                      watch_memory, raw_prefix, scan_current, raw_suffix, ii,
                      jj, copy_src, copy_dst, copy_memory) &&
                    clause_lits_pointer( ms_binary(Mscan), scratch_base) &&
                    Zlength(scratch_lits) == 2 &&
                    Znth(0, scratch_lits, 0) == tag_lit(scan_current) &&
                    Znth(1, scratch_lits, 0) == lit_neg_c(p) &&
                    IntArray::full( scratch_base, 2, scratch_lits) *
                    store(&(confl->size_learnt), int, 4) *
                    undef_data_at(&(confl->activity), float) *
                    enqueue_post_at(
                      s, values, levels_entry, tag_lit(scan_current),
                      tag_of_lit(p), ms_size(Mscan), ms_cap(Mscan),
                      ms_qtail(Mscan), 0, mt_assigns(ms_core(Mscan)),
                      mt_levels(ms_core(Mscan)), ms_reason_words(Mscan),
                      mt_trail(ms_core(Mscan)), mt_lim(ms_core(Mscan)),
                      ms_lim_cap(Mscan)) *
                    PtrArray::full( begin, Zlength(source_words), copy_memory) *
                    PtrArray::undef_seg(
                      begin, Zlength(source_words), scan_wcap) *
                    wlists_source_hole_handle(
                      s, wlists_entry, Zlength(scan_wm_pre), scan_wm_pre, scan_wm_post,
                      scan_caps_pre, scan_caps_post) *
                    clause_db_rep(ms_prob(Mscan)) *
                    clause_db_rep(ms_learnt(Mscan)) *
                    store(&(s->qhead), int, mt_qhead(ms_core(Mscan))) *
                    store(&(s->simpdb_props), int, simp_count) *
                    store(&(s->binary), clause *, ms_binary(Mscan)) *
                    store(&(s->stats.propagations), unsigned long long,
                          prop_count) *
                    store(&(s->stats.inspects), unsigned long long,
                          stats_inspects(ms_stats(Mscan))) *
                    solver_propagate_frame(s, Mscan) *
                    data_at(conflict_out, 0) *
                    undef_data_at(&(lits), lit *)
                    which implies
                    exists Mroute retained_route garbage_route,
                      propagation_binary_conflict_exit(
                        n, F, A_arr, K, M0, Mentry, Mscan, Mroute,
                        p, scan_current, confl,
                        source_words, retained, moved, rest, copy_memory,
                        garbage_route, retained_route) &&
                      minisat_propagation_reuse_scan(M0, Mroute, p, confl, nil) &&
                      ms_wm(Mroute) ==
                        app(scan_wm_pre, cons(retained_route, scan_wm_post)) &&
                      ms_wcaps(Mroute) ==
                        app(scan_caps_pre, cons(scan_wcap, scan_caps_post)) &&
                      Zlength(scan_wm_pre) == p &&
                      Zlength(scan_caps_pre) == p &&
                      ws == vecp_slot(wlists_entry, p) &&
                      endvar == begin + Zlength(source_words) &&
                      i == begin + Zlength(source_words) &&
                      j == begin + Zlength(retained_route) &&
                      simp_count == ms_simpdb_props(Mroute) &&
                      prop_count == stats_propagations(ms_stats(Mroute)) &&
                      0 <= Zlength(source_words) &&
                      Zlength(source_words) <= scan_wcap &&
                      0 < scan_wcap &&
                      scan_wcap <= INT_MAX &&
                      PtrArray::full(
                        begin, Zlength(source_words), copy_memory) *
                      PtrArray::undef_seg(
                        begin, Zlength(source_words), scan_wcap) *
                      wlists_source_hole_handle(
                        s, wlists_entry, Zlength(scan_wm_pre), scan_wm_pre, scan_wm_post,
                        scan_caps_pre, scan_caps_post) *
                      clause_db_rep(ms_prob(Mroute)) *
                      clause_db_rep(ms_learnt(Mroute)) *
                      store(&(s->qhead), int, mt_qhead(ms_core(Mroute))) *
                      store(&(s->levels), int *, levels_entry) *
                      solver_propagation_scan_arrays_noqh_at(
                        s, Mroute, values, s->reasons, levels_entry, s->trail,
                        ms_simpdb_props(Mroute),
                        stats_propagations(ms_stats(Mroute))) *
                      data_at(conflict_out, 0) *
                      has_permission(&(lits))
                 */
                /*@ Branch name binary_conflict */
                    // BREAK BRIDGE.  This is a verbatim copy of the scan loop's bottom merge
                    // assertion, plus `i >= endvar`.  The `break` below leaves the loop from
                    // this arm rather than falling through to that merge, so the same
                    // entailment is paid here and the loop-exit merge absorbs all three
                    // exits in one shape.
                /*@ Assert exists Mnext memory_next logical_next,
                          exists next_wm_pre next_wm_post,
                          exists next_caps_pre next_caps_post next_wcap,
                          exists retained_next moved_next rest_next garbage_next,
                          exists ii_next jj_next prop_count_next simp_count_next,
                          exists rsn_next lvl_next trl_next,
                          exists Mentry_next source_words_next,
                          i >= endvar &&
                          lvl_next == levels_entry &&
                          s == s@pre && conflict_out == conflict_out@pre &&
                  values == assigns_entry && solver_shape(Mnext) &&
                          msolver_seed_shadow(Mnext) &&
                          propagation_caller_frame(M0, Mnext) &&
                          propagation_scan_frontier( Mentry_next, Mnext, p) &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mnext, p, confl,
                            retained_next, rest_next) &&
                          minisat_propagation_reuse_scan(M0, Mnext, p, confl, rest_next) &&
                          propagation_watch_scan_physical(
                            source_words_next, retained_next, moved_next,
                            rest_next, garbage_next, memory_next,
                            ii_next, jj_next) &&
                          logical_next == app(retained_next, rest_next) &&
                          ms_wm(Mnext) ==
                            app(next_wm_pre,
                              cons(logical_next, next_wm_post)) &&
                          ms_wcaps(Mnext) ==
                            app(next_caps_pre,
                              cons(next_wcap, next_caps_post)) &&
                          Zlength(next_wm_pre) == p &&
                          Zlength(next_caps_pre) == p &&
                          ws == vecp_slot(wlists_entry, p) &&
                          endvar == begin + Zlength(source_words_next) &&
                          Zlength(memory_next) == Zlength(source_words_next) &&
                          i == begin + ii_next &&
                          j == begin + jj_next &&
                          0 <= jj_next && jj_next <= ii_next &&
                          0 <= ii_next &&
                          ii_next <= Zlength(source_words_next) &&
                          (ii_next != 0 ||
                           Mnext == msolver_propagation_scan_begin(
                             Mentry_next, simp_count_next, prop_count_next)) &&
                          simp_count_next == ms_simpdb_props(Mnext) &&
                          prop_count_next == stats_propagations(ms_stats(Mnext)) &&
                          0 <= Zlength(source_words_next) &&
                          Zlength(source_words_next) <= next_wcap &&
                          0 < next_wcap && next_wcap <= INT_MAX &&
                          store(&(ws->size), int, Zlength(source_words_next)) *
                          store(&(ws->cap), int, next_wcap) *
                          store(&(ws->ptr), void **, begin) *
                          PtrArray::full(
                            begin, Zlength(source_words_next), memory_next) *
                          PtrArray::undef_seg(
                            begin, Zlength(source_words_next), next_wcap) *
                          wlists_source_hole_handle(
                            s, wlists_entry, Zlength(next_wm_pre),
                            next_wm_pre, next_wm_post,
                            next_caps_pre, next_caps_post) *
                          clause_db_rep(ms_prob(Mnext)) *
                          clause_db_rep(ms_learnt(Mnext)) *
                          store(&(s->reasons), clause **, rsn_next) *
                          store(&(s->levels), int *, lvl_next) *
                          store(&(s->trail), lit *, trl_next) *
                          CharArray::seg(
                            values, 0, ms_size(Mnext),
                            mt_assigns(ms_core(Mnext))) *
                          CharArray::undef_seg(
                            values, ms_size(Mnext), ms_cap(Mnext)) *
                          store(&(s->qhead), int,
                            mt_qhead(ms_core(Mnext))) *
                          solver_propagation_scan_core_at(
                            s, Mnext, values, rsn_next, lvl_next, trl_next,
                            simp_count_next, prop_count_next) *
                          data_at(conflict_out, 0) *
                          has_permission(&(lits))
                     */
                    break;
                }
            /*@ Branch name binary_keep */
            // Same shape as the conflict-arm block above: `store(&i, clause **, i)` on
            // the RHS would havoc `i`, so the antisymmetric pin returns the cell with the
            // LHS's binder instead.  See the note there.
            /*@ begin + ii <= i && i <= begin + ii &&
                      data_at(i, Znth(ii, tagged_memory, 0)) *
                      PtrArray::missing_i(
                        begin, ii, 0, Zlength(source_words),
                        tagged_memory)
                    $ binary_keep
                    which implies
                    exists tagged_enqueue_success_memory,
                      tagged_enqueue_success_memory ==
                        replace_Znth(
                          ii,
                          Znth(ii, tagged_memory, 0),
                          tagged_memory) &&
                      begin + ii <= i && i <= begin + ii &&
                      PtrArray::full(
                        begin, Zlength(source_words),
                        tagged_enqueue_success_memory)
                    $ binary_keep
                 */
            // `enq_l == tag_lit(scan_current)` / `enq_reason == tag_of_lit(p)` must NOT be
            // written here.  A pure equation that DEFINES an LHS existential is solved
            // before the spatial match, so `enq_l` would be instantiated to
            // `tag_lit(scan_current)` (further rewritten by the canonicaliser) and could
            // no longer unify with the `enqueue` call's own retval spelling -- "Sep
            // cannot be fully solved" on the enqueue_post_at atom.  The antisymmetric
            // inequality pair below is not a defining equation, so it does not drive
            // instantiation ahead of the spatial match, yet still gives `enq_l ==
            // tag_lit(scan_current)` (resp. `enq_reason == tag_of_lit(p_v)`) by `lia`
            // once the spatial match has run.  `enq_reason` is pinned against
            // `tag_of_lit(p_v)`, a fresh ghost carried by `store(&p, int, p_v)`, rather
            // than naming `p` itself, because naming `p` in the pure part lets the
            // canonicaliser rewrite `p` inside this block's own counterweight and fails
            // the same way.  `store(&p, int, p_v)` is the counterweight for `p`'s cell,
            // which the RHS materialises via `tag_of_lit(p_v)`; it is safe here because
            // it is LHS-ONLY: the refresh trap only fires when `store(&x,T,x)` appears
            // on a RHS.
            /*@ exists enq_l enq_reason enq_ret p_v,
                  enq_ret != 0 &&
                  enq_l <= tag_lit(scan_current) &&
                  tag_lit(scan_current) <= enq_l &&
                  enq_reason <= tag_of_lit(p_v) &&
                  tag_of_lit(p_v) <= enq_reason &&
                  store(&p, int, p_v) *
                  enqueue_post_at(
                    s, values, levels_entry,
                    enq_l, enq_reason,
                    ms_size(Mscan), ms_cap(Mscan),
                    ms_qtail(Mscan), enq_ret,
                    mt_assigns(ms_core(Mscan)),
                    mt_levels(ms_core(Mscan)),
                    ms_reason_words(Mscan),
                    mt_trail(ms_core(Mscan)),
                    mt_lim(ms_core(Mscan)), ms_lim_cap(Mscan))
                $ binary_keep
                which implies
                  store(&p, int, p_v) *
                  enqueue_post_at(
                    s, values, levels_entry,
                    tag_lit(scan_current), tag_of_lit(p_v),
                    ms_size(Mscan), ms_cap(Mscan),
                    ms_qtail(Mscan), 1,
                    mt_assigns(ms_core(Mscan)),
                    mt_levels(ms_core(Mscan)),
                    ms_reason_words(Mscan),
                    mt_trail(ms_core(Mscan)),
                    mt_lim(ms_core(Mscan)), ms_lim_cap(Mscan))
                $ binary_keep
             */
            /*@ solver_propagation_scan_semantics(
                      n, F, A_arr, K, Mscan, p, 0,
                      retained, rest) &&
                minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                    tagged_word(scan_current) &&
                    rest == cons(scan_current, raw_suffix) &&
                    propagation_watch_scan_physical(source_words, retained,
                      moved, rest, garbage, watch_memory, ii, jj) &&
                    enqueue_post_at(
                      s, values, levels_entry,
                      tag_lit(scan_current), tag_of_lit(p),
                      ms_size(Mscan), ms_cap(Mscan),
                      ms_qtail(Mscan), 1,
                      mt_assigns(ms_core(Mscan)),
                      mt_levels(ms_core(Mscan)),
                      ms_reason_words(Mscan),
                      mt_trail(ms_core(Mscan)),
                      mt_lim(ms_core(Mscan)), ms_lim_cap(Mscan))
                    $ binary_keep
                    which implies
                    exists Mroute retained_route rest_route,
                      exists garbage_route memory_route,
                      retained_route ==
                        app(retained, cons(scan_current, nil)) &&
                      rest_route == raw_suffix &&
                      propagation_binary_keep_transition(
                        n, F, A_arr, K, Mscan, p,
                        scan_current, retained_route,
                        rest_route, Mroute) &&
                      minisat_propagation_reuse_scan(M0, Mroute, p, 0, rest_route) &&
                      propagation_scan_keep_step(
                        source_words, retained, moved, rest,
                        watch_memory, ii, jj, scan_current,
                        retained_route, rest_route,
                        garbage_route, memory_route) &&
                      enqueue_post_at(
                        s, values, levels_entry,
                        tag_lit(scan_current), tag_of_lit(p),
                        ms_size(Mscan), ms_cap(Mscan),
                        ms_qtail(Mscan), 1,
                        mt_assigns(ms_core(Mscan)),
                        mt_levels(ms_core(Mscan)),
                        ms_reason_words(Mscan),
                        mt_trail(ms_core(Mscan)),
                        mt_lim(ms_core(Mscan)),
                        ms_lim_cap(Mscan))
                    $ binary_keep
                 */
            }else{
                lit false_lit;
                lbool sig;

                /*@ solver_propagation_scan_semantics(
                      n, F, A_arr, K, Mscan, Zlength(scan_wm_pre), 0,
                      retained, rest) &&
                    minisat_propagation_reuse_scan(M0, Mscan, Zlength(scan_wm_pre), 0, rest) &&
                    propagation_watch_scan_physical(
                      source_words, retained, moved, rest, garbage,
                      watch_memory, ii, jj) &&
                    logical_words == app(retained, rest) &&
                    ms_wm(Mscan) ==
                      app(scan_wm_pre, cons(logical_words, scan_wm_post)) &&
                    watch_memory == app(raw_prefix, cons(scan_current, raw_suffix)) &&
                    Zlength(raw_prefix) == ii &&
                    clause_is_lit_result(scan_current, 0) &&
                    solver_shape(Mscan) &&
                    data_at(i, scan_current) *
                      clause_db_rep(ms_prob(Mscan)) *
                      clause_db_rep(ms_learnt(Mscan))
                    which implies
                    exists clause_contents,
                      3 <= Zlength(clause_contents) &&
                      Forall(lit_wf_c(n), clause_contents) &&
                      0 <= Znth(0, clause_contents, 0) &&
                      Znth(0, clause_contents, 0) < 2 * n &&
                      0 <= Znth(1, clause_contents, 0) &&
                      Znth(1, clause_contents, 0) < 2 * n &&
                      0 <= lit_var_c(Znth(0, clause_contents, 0)) &&
                      lit_var_c(Znth(0, clause_contents, 0)) < ms_size(Mscan) &&
                      0 <= lit_var_c(Znth(1, clause_contents, 0)) &&
                      lit_var_c(Znth(1, clause_contents, 0)) < ms_size(Mscan) &&
                      clause_db_pair_contents(ms_prob(Mscan), ms_learnt(Mscan),
                                              scan_current, clause_contents) &&
                      data_at(i, scan_current) *
                      clause_db_pair_focus(ms_prob(Mscan), ms_learnt(Mscan),
                                           scan_current, clause_contents)
                 */
                /*@ Given clause_contents */
                /*@ clause_db_pair_focus(ms_prob(Mscan), ms_learnt(Mscan),
                                         scan_current, clause_contents)
                    which implies
                      clause_db_pair_frame(ms_prob(Mscan), ms_learnt(Mscan),
                                           scan_current, clause_contents) *
                      IntArray::full(clause_lits_addr(scan_current),
                                     Zlength(clause_contents),
                                     clause_contents)
                 */
                lits = clause_begin(*i);

                // Make sure the false literal is data[1]:
                /*@ exists clause_base,
                      clause_lits_pointer(scan_current, clause_base) &&
                      2 <= Zlength(clause_contents) &&
                      lits == clause_base &&
                      IntArray::full(clause_base,
                                     Zlength(clause_contents),
                                     clause_contents)
                    which implies
                      clause_lits_pointer(scan_current, lits) &&
                      store(lits + 0 * sizeof(int), int,
                            Znth(0, clause_contents, 0)) *
                      store(lits + 1 * sizeof(int), int,
                            Znth(1, clause_contents, 0)) *
                      IntArray::seg(lits, 2,
                                    Zlength(clause_contents),
                                    sublist(2, Zlength(clause_contents),
                                            clause_contents))
                 */
                // NO local cell atoms in this block.  `store(&p, lit, p)` /
                // `store(&confl, clause *, confl)` on a `which implies` RHS would re-bind
                // the cell to a FRESH existential (`p_addr_NNNN_v`) with no equation to the
                // incoming value, leaving every downstream fact phrased over the old value
                // unusable and the VC in the shape `forall p_addr_v, p_addr_v = <old>`.
                // A value mention is not a cell touch, so nothing has to be re-emitted.
                // The RHS re-states the scan semantics in the exact spelling the k-loop
                // invariant below uses (`p` and the literal `0`, not `Zlength(scan_wm_pre)`
                // and `confl`) because QCP has no congruence closure.
                /*@ solver_propagation_scan_semantics(
                      n, F, A_arr, K, Mscan, Zlength(scan_wm_pre), confl,
                      retained, rest) &&
                    minisat_propagation_reuse_scan(M0, Mscan, Zlength(scan_wm_pre), confl, rest) &&
                    propagation_watch_scan_physical(
                      source_words, retained, moved, rest, garbage,
                      watch_memory, ii, jj) &&
                    logical_words == app(retained, rest) &&
                    ms_wm(Mscan) ==
                      app(scan_wm_pre, cons(logical_words, scan_wm_post)) &&
                    watch_memory == app(raw_prefix, cons(scan_current, raw_suffix)) &&
                    Zlength(raw_prefix) == ii &&
                    Zlength(scan_wm_pre) == p &&
                    clause_is_lit_result(scan_current, 0) &&
                    clause_db_pair_contents(ms_prob(Mscan), ms_learnt(Mscan),
                                            scan_current, clause_contents)
                    which implies
                    real_watch_pair(Zlength(scan_wm_pre), clause_contents) &&
                    (Znth(0, clause_contents, 0) == lit_neg_c(p) ||
                     Znth(1, clause_contents, 0) == lit_neg_c(p)) &&
                    rest == cons(scan_current, raw_suffix) &&
                    confl == 0 &&
                    solver_propagation_scan_semantics(
                      n, F, A_arr, K, Mscan, p, 0, retained, rest) &&
                    minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest)
                 */
                false_lit = lit_neg(p) /*@ where (original) */;
                if (lits[0] == false_lit){
                    lits[0] = lits[1];
                    lits[1] = false_lit;
                }
                // "slot 1 now holds false_lit" must be established EAGERLY (the assert
                // below is a hard stop, not a deferred VC).  The disjunction that does it
                // is produced by the `which implies` ABOVE, spelled over `p`: that block's
                // LHS carries `Zlength(scan_wm_pre) == p`, so its Coq VC -- the only layer
                // that can push an equality under `lit_neg_c` -- discharges it.  With the
                // disjunction spelled over `p`, the `Znth(0,cc) == lit_neg_c(p)` arm dies
                // here by a plain equality chain (`Znth(0,cc) != false_lit`, `false_lit ==
                // lit_neg_c(p)`); no congruence closure is needed.
                // `real_watch_pair` is deliberately NOT unfolded here into a second
                // disjunction spelled over `Zlength(scan_wm_pre)`: that arm is unrefutable
                // without congruence, and alongside the p-spelled disjunction the two
                // splits would form a 2x2 cross product one of whose cells has neither the
                // fact nor a refutation.
                // This block also CARRIES two facts about slot 0 across its own re-binding.
                // Its RHS re-binds `w0` to a fresh existential, which destroys the concrete
                // per-arm spelling (`Znth(0, clause_contents, 0)` on the no-swap path,
                // `Znth(1, clause_contents, 0)` after the swap) that every downstream ghost
                // for lits[0] unifies against.  Restating `0 <= w0 && w0 < 2 * n` here is
                // what lets the replacement-scan base case below derive `lit_wf_c n
                // watch0_base` (it is discharged on this LHS from the two unfolded slot
                // bounds put on the clause-focus RHS above, which hold on both arms).
                // `0 <= lit_sign_c(w0) && lit_sign_c(w0) <= 1` is added on the RHS only: it
                // is true by definition (`lit_sign_c l = if Z.odd l then 1 else 0`) so the
                // wit is a one-liner, and it is the fact that makes
                // `sig == 1 - 2 * lit_sign_c(watch0)` derivable after `sig = !lit_sign(...)`
                // -- symexec SPLITS on the `!`, and on the false arm it only learns
                // `lit_sign_c(w0) != 0`, which without this bound does not give `== 1`.
                // `w0 + w1 == Znth(0,cc,0) + Znth(1,cc,0)` is the NON-DISJUNCTIVE carrier
                // for "the two physical slots are the clause's two watches, possibly
                // swapped".  A pure `||` is not accepted on a `which implies` LHS, so the
                // multiset equality {w0,w1} = {cc[0],cc[1]} cannot be written
                // as the invariant's two-arm disjunction downstream.  The SUM is linear,
                // so symexec derives it on both arms of `if (lits[0] == false_lit)`:
                // no-swap gives w0 = Znth(0,cc,0), w1 = Znth(1,cc,0); after the swap
                // w0 = Znth(1,cc,0) and w1 = false_lit = Znth(0,cc,0) (the branch
                // condition).  With `real_watch_pair` (already carried here) and
                // `false_lit == lit_neg_c(p)` the sum RECOVERS the full disjunction in
                // Coq.
                // It is what the real-satisfied bridge below needs to show the database
                // lits update does not change this clause's contribution to watch list p.
                /*@ exists w0 w1,
                      w1 == lit_neg_c(p) &&
                      0 <= w0 && w0 < 2 * n &&
                      w0 + w1 ==
                        Znth(0, clause_contents, 0) +
                        Znth(1, clause_contents, 0) &&
                      real_watch_pair(Zlength(scan_wm_pre), clause_contents) &&
                      store(lits + 0 * sizeof(int), int, w0) *
                      store(lits + 1 * sizeof(int), int, w1)
                    which implies
                      w1 == lit_neg_c(p) &&
                      0 <= w0 && w0 < 2 * n &&
                      0 <= lit_sign_c(w0) && lit_sign_c(w0) <= 1 &&
                      w0 + w1 ==
                        Znth(0, clause_contents, 0) +
                        Znth(1, clause_contents, 0) &&
                      real_watch_pair(Zlength(scan_wm_pre), clause_contents) &&
                      store(lits + 0 * sizeof(int), int, w0) *
                      store(lits + 1 * sizeof(int), int, w1)
                 */
                assert(lits[1] == false_lit);
                //printf("checking clause: "); printlits(lits, lits+clause_size(*i)); printf("\n");

                // If 0th watch is true, then clause is already satisfied.
                sig = !lit_sign(lits[0]);
                sig = sig + sig - 1;
                if (values[lit_var(lits[0])] == sig){
                    *j = *i;
                    /*@ app(raw_prefix,
                          cons(scan_current, raw_suffix)) == watch_memory &&
                        Zlength(raw_prefix) == ii &&
                        ii <= jj && jj <= ii &&
                        propagation_ptr_segment(
                          begin, 0, ii, raw_prefix) *
                        data_at(
                          begin + ii * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, ii + 1,
                          Zlength(source_words), raw_suffix)
                        $ scan_same
                        which implies
                        PtrArray::full(
                          begin, Zlength(source_words),
                          replace_Znth(
                            jj, scan_current, watch_memory))
                        $ scan_same
                     */
                    /*@ app(raw_prefix,
                          cons(scan_current, raw_suffix)) == watch_memory &&
                        Zlength(raw_prefix) == ii &&
                        0 <= jj && jj < ii &&
                        propagation_ptr_segment(
                          begin, 0, jj,
                          sublist(0, jj, raw_prefix)) *
                        data_at(
                          begin + jj * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, jj + 1, ii,
                          sublist(jj + 1, ii, raw_prefix)) *
                        data_at(
                          begin + ii * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, ii + 1,
                          Zlength(source_words), raw_suffix)
                        $ scan_move
                        which implies
                        PtrArray::full(
                          begin, Zlength(source_words),
                          replace_Znth(
                            jj, scan_current, watch_memory))
                        $ scan_move
                     */
                    j++;
                // The RHS's
                // `propagation_real_satisfied_transition` moves `scan_current` from
                // `pending` into `scanned` inside `minisat_focus_scan_carrier`, which
                // demands `minisat_occurrence_safe` for that occurrence -- i.e. "slot 0 is
                // assigned TRUE", the enclosing `if (values[lit_var(lits[0])] == sig)`
                // condition.  A which_implies_wit sees no ambient path condition, so it has
                // to be written here.  `sig = !lit_sign(lits[0]); sig = sig + sig - 1;`
                // makes symexec SPLIT on `!lit_sign` (see the note at the two array folds
                // above), so on one path the state knows `lit_sign_c(watch0) == 0 && sig ==
                // 1` and on the other `lit_sign_c(watch0) != 0 && sig == -1`; `lit_sign_c`
                // is an opaque Extern Coq function, so the merged form
                // `sig == 1 - 2 * lit_sign_c(watch0)` is NOT derivable on the second path.
                // It is made derivable on the second path by `0 <= lit_sign_c(w0) &&
                // lit_sign_c(w0) <= 1` carried on the re-binding block's RHS above.
                // Since `lit_sign_c l = if Z.odd l then 1 else 0` and
                // `lit_sig l = if Z.odd l then -1 else 1`, the two conjuncts
                // `sig == 1 - 2 * lit_sign_c(watch0)` and
                // `Znth(lit_var_c(watch0), mt_assigns(ms_core(Mscan)), 0) == sig` are
                // exactly `lit_true(mt_assigns(ms_core(Mscan)), watch0)` in Coq.
                // SECOND GAP: `minisat_occurrence_safe` is about the
                // occurrence of the clause in the UPDATED database, and the carrier's
                // permutation only transfers from `ms_prob/ms_learnt(Mscan)` to
                // `prob_route/learnt_route` if the `db_pair_lits_update` does not change
                // this clause's contribution to watch list `p` -- i.e. only if
                // {watch0, false_lit} is the same multiset as {cc[0], cc[1]}.  That is the
                // replacement-scan invariant's two-arm disjunction, which
                // CANNOT be written on a `which implies` LHS (`||` is rejected there).
                // It is carried instead as the linear sum below plus `real_watch_pair`,
                // which together recover the disjunction in Coq.
                // `3 <= Zlength(clause_contents)` (available from this loop's own Inv Assert) is what makes
                // `Zlength(propagation_normalized_clause(...)) == Zlength(clause_contents)`,
                // needed to match the sealed header word when refolding `clause_db_rep`.
                // None of these conjuncts defines `watch0`, so none can drive premature
                // instantiation ahead of the spatial match against lits[0].
                /*@ exists watch0,
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0,
                            retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          rest == cons(scan_current, raw_suffix) &&
                          propagation_watch_scan_physical(
                            source_words, retained, moved, rest, garbage,
                            watch_memory, ii, jj) &&
                          clause_lits_pointer(scan_current, lits) &&
                          3 <= Zlength(clause_contents) &&
                          real_watch_pair(Zlength(scan_wm_pre), clause_contents) &&
                          Zlength(scan_wm_pre) == p &&
                          false_lit == lit_neg_c(p) &&
                          watch0 + false_lit ==
                            Znth(0, clause_contents, 0) +
                            Znth(1, clause_contents, 0) &&
                          sig == 1 - 2 * lit_sign_c(watch0) &&
                          Znth(lit_var_c(watch0),
                               mt_assigns(ms_core(Mscan)), 0) == sig &&
                          clause_db_pair_frame(
                            ms_prob(Mscan), ms_learnt(Mscan),
                            scan_current, clause_contents) *
                          store(lits + 0 * sizeof(int), int, watch0) *
                          store(lits + 1 * sizeof(int), int, false_lit) *
                          IntArray::seg(
                            lits, 2, Zlength(clause_contents),
                            sublist(2, Zlength(clause_contents),
                                    clause_contents))
                        which implies
                        exists watch0 prob_route learnt_route Mroute,
                          exists retained_route rest_route,
                          exists garbage_route memory_route,
                          db_pair_lits_update(
                            ms_prob(Mscan), ms_learnt(Mscan),
                            scan_current, clause_contents,
                            propagation_normalized_clause(
                              watch0, false_lit, clause_contents),
                            prob_route, learnt_route) &&
                          retained_route ==
                            app(retained, cons(scan_current, nil)) &&
                          rest_route == raw_suffix &&
                          propagation_real_satisfied_transition(
                            n, F, A_arr, K, Mscan, p,
                            prob_route, learnt_route,
                            retained_route, rest_route, Mroute) &&
                          minisat_propagation_reuse_scan(M0, Mroute, p, 0, rest_route) &&
                          propagation_scan_keep_step(
                            source_words, retained, moved, rest,
                            watch_memory, ii, jj, scan_current,
                            retained_route, rest_route,
                            garbage_route, memory_route) &&
                          clause_db_rep(prob_route) *
                          clause_db_rep(learnt_route) *
                          has_permission(&lits) *
                          has_permission(&sig)
                     */
                /*@ Given watch0 prob_route learnt_route Mroute retained_route rest_route */
                /*@ Branch name real_satisfied */
                }else{
                    // Look for new watch:
                    /* Keep the ii-th watch cell OPEN across the `clause_size(*i)` read.
                       Folding to PtrArray::full here and re-opening it by hand (an earlier
                       hand-open in this same loop) handed the cell to the BUILTIN PtrArray post
                       close rules: the hand-open's value `scan_current` is not the `l[i]`
                       spelling the READ-close (id 2) requires, so the WRITE-close (id 3)
                       fired instead and re-spelled the array as
                       replace_Znth(ii, scan_current, watch_memory).  `*i` then evaluated
                       to replace_Znth(...)[ii], a different spatial key from the
                       `scan_current`-keyed clause header unfolded just below, and QCP has
                       no congruence closure -- fatal at clause_size's precondition.
                       propagation_ptr_segment is an opaque Extern Coq assertion that
                       appears in no strategy rule, so while the remainder stays in that
                       form no builtin rule can close the cell and `*i` keeps evaluating
                       to `scan_current`.  The fold to PtrArray::full therefore happens
                       AFTER the read instead of before it. */
                    /*@ clause_db_pair_frame(
                          ms_prob(Mscan), ms_learnt(Mscan),
                          scan_current, clause_contents)
                        which implies exists (is_learnt_scan : bool),
                          clause_hdr_word(
                            is_learnt_scan,
                            Zlength(clause_contents)) / 2 ==
                              Zlength(clause_contents) &&
                          store(clause_hdr_addr(scan_current), int,
                                clause_hdr_word(
                                  is_learnt_scan,
                                  Zlength(clause_contents))) *
                          activity_state(scan_current, is_learnt_scan) *
                          clause_db_pair_remainder(
                            ms_prob(Mscan), ms_learnt(Mscan),
                            scan_current, is_learnt_scan, clause_contents)
                     */
                    /*@ Given is_learnt_scan */
                    lit* stop = lits + clause_size(*i);
                    /*@ store(clause_hdr_addr(scan_current), int,
                              clause_hdr_word(
                                is_learnt_scan,
                                Zlength(clause_contents))) *
                        activity_state(scan_current, is_learnt_scan) *
                        clause_db_pair_remainder(
                          ms_prob(Mscan), ms_learnt(Mscan),
                          scan_current, is_learnt_scan, clause_contents)
                        which implies
                        clause_db_pair_frame(
                          ms_prob(Mscan), ms_learnt(Mscan),
                          scan_current, clause_contents)
                     */
                    // No join here either: both arms below already produce exactly this
                    // PtrArray::full shape, and merging would demand that the pure facts
                    // agree, which the !lit_sign case split makes impossible.
                    /*@ app(raw_prefix,
                          cons(scan_current, raw_suffix)) == watch_memory &&
                        Zlength(raw_prefix) == ii &&
                        propagation_ptr_segment(
                          begin, 0, ii, raw_prefix) *
                        data_at(
                          begin + ii * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, ii + 1,
                          Zlength(source_words), raw_suffix)
                        $ scan_same
                        which implies
                        PtrArray::full(
                          begin, Zlength(source_words), watch_memory)
                        $ scan_same
                     */
                    /*@ app(raw_prefix,
                          cons(scan_current, raw_suffix)) == watch_memory &&
                        Zlength(raw_prefix) == ii &&
                        0 <= jj && jj < ii &&
                        propagation_ptr_segment(
                          begin, 0, jj,
                          sublist(0, jj, raw_prefix)) *
                        data_at(
                          begin + jj * sizeof(struct clause_t *),
                          struct clause_t *, Znth(jj, raw_prefix, 0)) *
                        propagation_ptr_segment(
                          begin, jj + 1, ii,
                          sublist(jj + 1, ii, raw_prefix)) *
                        data_at(
                          begin + ii * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, ii + 1,
                          Zlength(source_words), raw_suffix)
                        $ scan_move
                        which implies
                        PtrArray::full(
                          begin, Zlength(source_words), watch_memory)
                        $ scan_move
                     */
                    /*@ PtrArray::full(
                          begin, Zlength(source_words), watch_memory)
                        which implies
                        exists candidate_post_memory,
                          candidate_post_memory == watch_memory &&
                          PtrArray::full(
                            begin, Zlength(source_words),
                            candidate_post_memory)
                     */
                    /*@ Given candidate_post_memory */
                    lit* k;
                    // Base case of the replacement scan.  `propagation_replacement_scan_inv`
                    // is an opaque Coq Prop: ordinary assertions cannot derive it, so the
                    // k == 2 instance has to be introduced by a `which implies` whose LHS
                    // carries its premises (they become hypotheses of the isolated
                    // which_implies_wit AND an obligation where the ambient is available).
                    // `watch0` is bound spatially off lits[0] so the invariant's `watch0`
                    // and this one are the same term.
                    // The RHS's
                    // `propagation_replacement_scan_inv` needs `Forall (lit_wf_c n) words`
                    // with `words = watch0_base :: false_lit :: sublist 2 ...`, i.e.
                    // `0 <= watch0_base < 2*n` for a which_implies_wit-FORALL-bound ghost.
                    // `Forall(lit_wf_c(n), clause_contents)` alone says nothing about a free
                    // `watch0_base`, so without the bound below the wit reads
                    // `forall watch0_base, ... |-- 0 <= watch0_base < 2*n`, which is false.
                    // The loop invariant's two-arm disjunction
                    //   ((watch0_base == Znth(0,cc,0) && false_lit == Znth(1,cc,0)) || ...)
                    // cannot simply be copied onto this LHS: it is rejected as "Multiple
                    // cases inside pre- or post-condition".
                    // A pure `||` is legal in an `Inv Assert`/`Assert` and on a `which implies` RHS
                    // (the enqueue-conflict RHS earlier in this function does exactly that), but NOT on
                    // a `which implies` LHS -- it would be a multi-case precondition.
                    // What is written instead is the disjunction's only consequence that
                    // matters here, in non-disjunctive form.  It is discharged at symexec
                    // time from the two unfolded slot bounds added to the clause-focus RHS
                    // (`0 <= Znth(k, clause_contents, 0) < 2 * n`, k = 0,1) carried across
                    // the lits[0]/lits[1] re-binding block by its `0 <= w0 && w0 < 2 * n`.
                    // An inequality cannot drive premature instantiation, so the spatial
                    // match of `watch0_base` against lits[0] is unaffected.
                    /*@ exists watch0_base,
                          0 <= watch0_base && watch0_base < 2 * n &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0, retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          propagation_scan_frontier(Mentry, Mscan, p) &&
                          solver_shape(Mscan) &&
                          real_watch_pair(Zlength(scan_wm_pre), clause_contents) &&
                          Zlength(scan_wm_pre) == p &&
                          Forall(lit_wf_c(n), clause_contents) &&
                          3 <= Zlength(clause_contents) &&
                          false_lit == lit_neg_c(p) &&
                          store(lits + 0 * sizeof(int), int, watch0_base) *
                          store(lits + 1 * sizeof(int), int, false_lit)
                        which implies
                          Zlength(scan_wm_pre) <= p &&
                          p <= Zlength(scan_wm_pre) &&
                          propagation_replacement_scan_inv(
                            n, Mscan, false_lit,
                            propagation_normalized_clause(watch0_base, false_lit,
                              clause_contents), 2) &&
                          store(lits + 0 * sizeof(int), int, watch0_base) *
                          store(lits + 1 * sizeof(int), int, false_lit)
                     */
                    // The levels array below is keyed on the `With` ghost `levels_entry`
                    // with an explicit `store(&(s->levels), int *, levels_entry)`, NOT on
                    // the field read `s->levels`.  A field read in an assertion
                    // materialises a FRESH existential (the state then carries
                    // `store(&(s->levels), s_value_levels_<k>, int*)` and
                    // `IntArray.seg(s_value_levels_<k>, ...)`), and every downstream
                    // consumer in the unit-clause arm -- the `enqueue_state_at` bridge
                    // below and `enqueue`'s own spec -- spells it `levels_entry`, which is
                    // universally fixed and so cannot unify with that existential.
                    // `s->reasons` / `s->trail` are NOT affected and are left alone: every
                    // consumer binds them with its own `exists rsn trl`, and an
                    // existential unifies with `s_value_reasons_*` freely.  The enclosing
                    // watcher-scan `Inv Assert` already uses the ghost spelling; this
                    // block had simply diverged from it.
                    /*@ Inv Assert exists offset watch0,
                          s == s@pre && conflict_out == conflict_out@pre &&
                          values == assigns_entry &&
                          solver_shape(Mscan) &&
                          msolver_seed_shadow(Mscan) &&
                          propagation_caller_frame(M0, Mscan) &&
                          propagation_scan_frontier(Mentry, Mscan, p) &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0, retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          simp_count == ms_simpdb_props(Mscan) &&
                          prop_count == stats_propagations(ms_stats(Mscan)) &&
                          propagation_watch_scan_physical(
                            source_words, retained, moved, rest, garbage,
                            watch_memory, ii, jj) &&
                          rest == cons(scan_current, raw_suffix) &&
                          confl == 0 &&
                          endvar == begin + Zlength(source_words) &&
                          i == begin + ii &&
                          j == begin + jj &&
                          0 <= jj &&
                          jj <= ii &&
                          0 <= ii &&
                          ii < Zlength(source_words) &&
                          0 <= scan_current &&
                          watch_memory ==
                            app(raw_prefix, cons(scan_current, raw_suffix)) &&
                          Zlength(raw_prefix) == ii &&
                          candidate_post_memory == watch_memory &&
                          Znth(ii, candidate_post_memory, 0) ==
                            scan_current &&
                          logical_words == app(retained, rest) &&
                          ms_wm(Mscan) ==
                            app(scan_wm_pre,
                                cons(logical_words, scan_wm_post)) &&
                          ms_wcaps(Mscan) ==
                            app(scan_caps_pre,
                                cons(scan_wcap, scan_caps_post)) &&
                          Zlength(scan_wm_pre) == p &&
                          Zlength(scan_caps_pre) == p &&
                          ws == vecp_slot(wlists_entry, p) &&
                          clause_lits_pointer(scan_current, lits) &&
                          3 <= Zlength(clause_contents) &&
                          false_lit == lit_neg_c(p) &&
                          real_watch_pair(
                            Zlength(scan_wm_pre), clause_contents) &&
                          watch0 + false_lit ==
                            Znth(0, clause_contents, 0) +
                            Znth(1, clause_contents, 0) &&
                          stop == lits + Zlength(clause_contents) &&
                          k == lits + offset &&
                          2 <= offset &&
                          offset <= Zlength(clause_contents) &&
                          propagation_replacement_scan_inv(
                            n, Mscan, false_lit,
                            propagation_normalized_clause(watch0, false_lit,
                              clause_contents), offset) &&
                          -1 <= sig &&
                          sig <= 1 &&
                          0 <= Zlength(source_words) &&
                          Zlength(source_words) <= scan_wcap &&
                          0 < scan_wcap &&
                          scan_wcap <= INT_MAX &&
                          PtrArray::full(
                            begin, Zlength(source_words),
                            candidate_post_memory) *
                          store(&(ws->size), int, Zlength(source_words)) *
                          store(&(ws->cap), int, scan_wcap) *
                          store(&(ws->ptr), void **, begin) *
                          PtrArray::undef_seg(
                            begin, Zlength(source_words), scan_wcap) *
                          wlists_source_hole_handle(
                            s, wlists_entry, Zlength(scan_wm_pre), scan_wm_pre,
                            scan_wm_post, scan_caps_pre, scan_caps_post) *
                          clause_db_pair_frame(
                            ms_prob(Mscan), ms_learnt(Mscan), scan_current,
                            clause_contents) *
                          store(lits + 0 * sizeof(int), int, watch0) *
                          store(lits + 1 * sizeof(int), int, false_lit) *
                          IntArray::seg(
                            lits, 2, Zlength(clause_contents),
                            sublist(2, Zlength(clause_contents),
                                    clause_contents)) *
                          CharArray::seg(
                            values, 0, ms_size(Mscan),
                            mt_assigns(ms_core(Mscan))) *
                          CharArray::undef_seg(
                            values, ms_size(Mscan), ms_cap(Mscan)) *
                          store(&(s->levels), int *, levels_entry) *
                          store(&(s->qhead), int, mt_qhead(ms_core(Mscan))) *
                          store(&(s->reasons), clause **, rsn_scan) *
                          store(&(s->trail), lit *, trl_scan) *
                          solver_propagation_scan_core_at(
                            s, Mscan, values, rsn_scan, levels_entry,
                            trl_scan, simp_count, prop_count) *
                          data_at(conflict_out, 0)
                     */
                    // `has_permission(&sig)` was deleted here: in a FULL assertion a
                    // value mention of `sig` (`-1 <= sig && sig <= 1` above) already
                    // materialises the cell, so writing has_permission beside it demands
                    // a SECOND cell at the same address and the loop-entry SEP can never
                    // be solved.  (The `&#sig` sites are different: there an INNER `sig`
                    // shadows this one, so two cells genuinely exist.)
                    for (k = lits + 2; k < stop; k++){
                        // No `Given candidate_post_memory` here: a `Given` may not
                        // re-declare a logical name that is still live, and this one is
                        // live from the `which implies` above the loop.  Only `watch0`
                        // is fresh (it is bound by this loop's own `Inv Assert exists`).
                        /*@ Given watch0 offset */
                        /*@ k == lits + offset &&
                              2 <= offset &&
                              offset < Zlength(clause_contents) &&
                              IntArray::seg(
                                lits, 2, Zlength(clause_contents),
                                sublist(2, Zlength(clause_contents),
                                        clause_contents))
                            which implies
                            exists candidate,
                              k == lits + offset &&
                              2 <= offset &&
                              offset < Zlength(clause_contents) &&
                              candidate ==
                                Znth(offset - 2,
                                  sublist(2, Zlength(clause_contents),
                                          clause_contents), 0) &&
                              data_at(k, candidate) *
                              propagation_int_missing(
                                lits, offset, 2,
                                Zlength(clause_contents),
                                sublist(2, Zlength(clause_contents),
                                        clause_contents))
                         */
                        /*@ Given candidate */
                        /*@ 0 <= lit_var_c(candidate) &&
                              lit_var_c(candidate) < ms_size(Mscan)
                         */
                        lbool sig = lit_sign(*k);
                        sig = sig + sig - 1;
                        if (values[lit_var(*k)] != sig){
                            /*@ 0 <= lit_var_c(candidate) &&
                                  lit_var_c(candidate) < ms_size(Mscan)
                                which implies
                                0 <= lit_neg_c(candidate) &&
                                lit_neg_c(candidate) <
                                  2 * ms_size(Mscan)
                             */
                            // `solver_read_wlist` asks for the FOLDED field handle, but
                            // mid-scan the watch table is held as
                            // `wlists_source_hole_handle`, which is definitionally
                            // `solver_wlists_handle ** wlists_rep_from(0..) **
                            // wlists_rep_from(hole+1..)`, defined in solver_qcp_lib.v.  Split it, make the
                            // call, fold straight back -- the same idiom the scan-head
                            // call uses against `store(&(s->wlists), ...)`.
                            /*@ wlists_source_hole_handle(
                                  s, wlists_entry, Zlength(scan_wm_pre),
                                  scan_wm_pre, scan_wm_post,
                                  scan_caps_pre, scan_caps_post)
                                which implies
                                solver_wlists_handle(s, wlists_entry) *
                                wlists_rep_from(wlists_entry, 0, scan_wm_pre, scan_caps_pre) *
                                wlists_rep_from(wlists_entry, Zlength(scan_wm_pre) + 1,
                                                scan_wm_post, scan_caps_post)
                             */
                            vecp *destination = solver_read_wlist(
                              s, lit_neg(*k) /*@ where (original) */)
                              /*@ where rdw_wl = wlists_entry */;
                            /* The three reads of `*k' above share one exact
                               cell.  Re-expose the ordinary missing segment
                               only after the last read, before any branch may
                               update the selected literal. */
                            /*@ data_at(k, candidate) *
                                propagation_int_missing(
                                  lits, offset, 2,
                                  Zlength(clause_contents),
                                  sublist(2, Zlength(clause_contents),
                                          clause_contents))
                                which implies
                                data_at(k, candidate) *
                                IntArray::missing_i(
                                  lits, offset, 2,
                                  Zlength(clause_contents),
                                  sublist(2, Zlength(clause_contents),
                                          clause_contents))
                             */
                            /*@ solver_wlists_handle(s, wlists_entry) *
                                wlists_rep_from(wlists_entry, 0, scan_wm_pre, scan_caps_pre) *
                                wlists_rep_from(wlists_entry, Zlength(scan_wm_pre) + 1,
                                                scan_wm_post, scan_caps_post)
                                which implies
                                wlists_source_hole_handle(
                                  s, wlists_entry, Zlength(scan_wm_pre),
                                  scan_wm_pre, scan_wm_post,
                                  scan_caps_pre, scan_caps_post)
                             */
                            /*@ solver_shape(Mscan) &&
                                  ms_wm(Mscan) ==
                                    app(scan_wm_pre,
                                      cons(logical_words, scan_wm_post)) &&
                                  ms_wcaps(Mscan) ==
                                    app(scan_caps_pre, cons(scan_wcap, scan_caps_post)) &&
                                  Zlength(scan_caps_pre) == Zlength(scan_wm_pre)
                                which implies
                                Zlength(scan_caps_pre) == Zlength(scan_wm_pre) &&
                                Zlength(scan_caps_post) == Zlength(scan_wm_post) &&
                                Zlength(scan_wm_pre) + 1 +
                                  Zlength(scan_wm_post) == 2 * ms_size(Mscan)
                             */
                            /*@ solver_propagation_scan_semantics(
                                  n, F, A_arr, K, Mscan,
                                  Zlength(scan_wm_pre), confl,
                                  retained, rest) &&
                                minisat_propagation_reuse_scan(M0, Mscan, Zlength(scan_wm_pre), confl, rest) &&
                                  real_watch_pair(
                                    Zlength(scan_wm_pre), clause_contents) &&
                                  2 <= offset &&
                                  offset < Zlength(clause_contents) &&
                                  candidate ==
                                    Znth(offset - 2,
                                      sublist(2,
                                        Zlength(clause_contents),
                                        clause_contents), 0) &&
                                  clause_db_pair_frame(
                                    ms_prob(Mscan), ms_learnt(Mscan),
                                    scan_current, clause_contents)
                                which implies
                                solver_propagation_scan_semantics(
                                  n, F, A_arr, K, Mscan,
                                  Zlength(scan_wm_pre), confl,
                                  retained, rest) &&
                                minisat_propagation_reuse_scan(M0, Mscan, Zlength(scan_wm_pre), confl, rest) &&
                                propagation_destination_index(
                                  2 * ms_size(Mscan), Zlength(scan_wm_pre),
                                  lit_neg_c(candidate)) &&
                                clause_db_pair_frame(
                                  ms_prob(Mscan), ms_learnt(Mscan),
                                  scan_current, clause_contents)
                             */
                            /*@ propagation_destination_index(
                                  2 * ms_size(Mscan), Zlength(scan_wm_pre),
                                  lit_neg_c(candidate)) &&
                                  Zlength(scan_wm_pre) + 1 +
                                    Zlength(scan_wm_post) == 2 * ms_size(Mscan) &&
                                  Zlength(scan_caps_pre) == Zlength(scan_wm_pre) &&
                                  Zlength(scan_caps_post) == Zlength(scan_wm_post) &&
                                  destination ==
                                    vecp_slot(wlists_entry, lit_neg_c(candidate)) &&
                                  wlists_source_hole_handle(
                                    s, wlists_entry, Zlength(scan_wm_pre),
                                    scan_wm_pre, scan_wm_post,
                                    scan_caps_pre, scan_caps_post)
                                which implies
                                wlists_destination_handle(
                                  s, wlists_entry, Zlength(scan_wm_pre),
                                  lit_neg_c(candidate), destination,
                                  scan_wm_pre, scan_wm_post,
                                  scan_caps_pre, scan_caps_post)
                             */
                            /*@ wlists_destination_handle(
                                  s, wlists_entry, Zlength(scan_wm_pre),
                                  lit_neg_c(candidate), destination,
                                  scan_wm_pre, scan_wm_post,
                                  scan_caps_pre, scan_caps_post)
                                which implies
                                solver_wlists_handle(s, wlists_entry) *
                                wlists_split_except_two(
                                  wlists_entry, Zlength(scan_wm_pre),
                                  lit_neg_c(candidate),
                                  scan_wm_pre, scan_wm_post,
                                  scan_caps_pre, scan_caps_post) *
                                vecp_rep(
                                  destination,
                                  wlists_split_target_words(
                                    Zlength(scan_wm_pre),
                                    lit_neg_c(candidate),
                                    scan_wm_pre, scan_wm_post),
                                  wlists_split_target_cap(
                                    Zlength(scan_wm_pre),
                                    lit_neg_c(candidate),
                                    scan_caps_pre, scan_caps_post))
                             */
                            if (vecp_reserve(destination)
                                  /*@ where l = wlists_split_target_words(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_wm_pre, scan_wm_post) */ ==
                                -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) {
                                /*@ exists destination_ptr,
                                    vector_capacity_exhausted(
                                      Zlength(wlists_split_target_words(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_wm_pre, scan_wm_post)),
                                      wlists_split_target_cap(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_caps_pre, scan_caps_post)) &&
                                    store(&(destination->size), int,
                                      Zlength(wlists_split_target_words(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_wm_pre, scan_wm_post))) *
                                    store(&(destination->cap), int,
                                      wlists_split_target_cap(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_caps_pre, scan_caps_post)) *
                                    store(&(destination->ptr), void **,
                                          destination_ptr) *
                                    PtrArray::seg(destination_ptr, 0,
                                      Zlength(wlists_split_target_words(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_wm_pre, scan_wm_post)),
                                      wlists_split_target_words(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_wm_pre, scan_wm_post)) *
                                    PtrArray::undef_seg(destination_ptr,
                                      Zlength(wlists_split_target_words(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_wm_pre, scan_wm_post)),
                                      wlists_split_target_cap(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_caps_pre, scan_caps_post))
                                    which implies
                                    vector_capacity_exhausted(
                                      Zlength(wlists_split_target_words(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_wm_pre, scan_wm_post)),
                                      wlists_split_target_cap(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_caps_pre, scan_caps_post)) &&
                                    vecp_rep(
                                      destination,
                                      wlists_split_target_words(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_wm_pre, scan_wm_post),
                                      wlists_split_target_cap(
                                        Zlength(scan_wm_pre),
                                        lit_neg_c(candidate),
                                        scan_caps_pre, scan_caps_post))
                                 */
                                /*@ i == begin + ii &&
                                      j == begin + jj &&
                                      0 <= jj && jj <= ii &&
                                      0 <= ii &&
                                      ii < Zlength(source_words) &&
                                      PtrArray::full(
                                        begin, Zlength(source_words),
                                        candidate_post_memory)
                                    which implies
                                    ((jj == ii &&
                                      i == begin + ii &&
                                      j == begin + jj &&
                                      j == i &&
                                      propagation_ptr_segment(
                                        begin, 0, ii,
                                        sublist(
                                          0, ii,
                                          candidate_post_memory)) *
                                      data_at(
                                        begin + ii * sizeof(struct clause_t *),
                                        struct clause_t *,
                                        Znth(
                                          ii,
                                          candidate_post_memory, 0)) *
                                      propagation_ptr_segment(
                                        begin, ii + 1,
                                        Zlength(source_words),
                                        sublist(ii + 1,
                                          Zlength(source_words),
                                          candidate_post_memory))) ||
                                     (jj < ii &&
                                      i == begin + ii &&
                                      j == begin + jj &&
                                      propagation_ptr_segment(
                                        begin, 0, jj,
                                        sublist(
                                          0, jj,
                                          candidate_post_memory)) *
                                      data_at(
                                        begin + jj * sizeof(struct clause_t *),
                                        struct clause_t *,
                                        Znth(
                                          jj,
                                          candidate_post_memory, 0)) *
                                      propagation_ptr_segment(
                                        begin, jj + 1, ii,
                                        sublist(jj + 1, ii,
                                          candidate_post_memory)) *
                                      data_at(
                                        begin + ii * sizeof(struct clause_t *),
                                        struct clause_t *,
                                        Znth(
                                          ii,
                                          candidate_post_memory, 0)) *
                                      propagation_ptr_segment(
                                        begin, ii + 1,
                                        Zlength(source_words),
                                        sublist(ii + 1,
                                          Zlength(source_words),
                                          candidate_post_memory))))
                                    $ capacity_same capacity_move
                                 */
                                *j = *i;
                                /*@ Znth(ii, candidate_post_memory, 0) ==
                                      scan_current &&
                                    Zlength(candidate_post_memory) ==
                                      Zlength(source_words) &&
                                    ii <= jj && jj <= ii &&
                                    propagation_ptr_segment(
                                      begin, 0, ii,
                                      sublist(
                                        0, ii,
                                        candidate_post_memory)) *
                                    data_at(
                                      begin + ii * sizeof(struct clause_t *),
                                      struct clause_t *, Znth(
                                        ii,
                                        candidate_post_memory, 0)) *
                                    propagation_ptr_segment(
                                      begin, ii + 1,
                                      Zlength(source_words),
                                      sublist(ii + 1,
                                        Zlength(source_words),
                                        candidate_post_memory))
                                    $ capacity_same
                                    which implies
                                    PtrArray::full(
                                      begin, Zlength(source_words),
                                      replace_Znth(
                                        jj, scan_current,
                                        candidate_post_memory))
                                    $ capacity_same
                                 */
                                /*@ Znth(ii, candidate_post_memory, 0) == scan_current &&
                                    Zlength(candidate_post_memory) ==
                                      Zlength(source_words) &&
                                    propagation_ptr_segment(
                                      begin, 0, jj,
                                      sublist(
                                        0, jj,
                                        candidate_post_memory)) *
                                    data_at(
                                      begin + jj * sizeof(struct clause_t *),
                                      struct clause_t *, scan_current) *
                                    propagation_ptr_segment(
                                      begin, jj + 1, ii,
                                      sublist(jj + 1, ii,
                                        candidate_post_memory)) *
                                    data_at(
                                      begin + ii * sizeof(struct clause_t *),
                                      struct clause_t *, scan_current) *
                                    propagation_ptr_segment(
                                      begin, ii + 1,
                                      Zlength(source_words),
                                      sublist(ii + 1,
                                        Zlength(source_words),
                                        candidate_post_memory))
                                    $ capacity_move
                                    which implies
                                    PtrArray::full(
                                      begin, Zlength(source_words),
                                      replace_Znth(
                                        jj, scan_current,
                                        candidate_post_memory))
                                    $ capacity_move
                                 */
                                /* The two paths have different private arithmetic facts but the
                                   same semantic copy state.  Give them one group name so the full
                                   loop invariant below, rather than a partial join, abstracts those
                                   private facts in V2.1.0. */
                                /*@ Branch name
                                    capacity_copy: 0 <= jj && jj <= ii
                                 */
                                j++;
                                i++;
                                /*@ Inv Assert exists copy_memory copy_src copy_dst,
                                      s == s@pre && conflict_out == conflict_out@pre &&
                                      values == assigns_entry &&
                                      propagation_scan_open(
                                        n, F, A_arr, K, M0, Mentry, Mscan, p,
                                        confl, source_words, retained, moved,
                                        rest, garbage, watch_memory, ii, jj,
                                        scan_current, raw_suffix) &&
                                      minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
                                      endvar == begin + Zlength(source_words) &&
                                      i == begin + copy_src &&
                                      j == begin + copy_dst &&
                                      0 <= copy_dst &&
                                      copy_dst <= copy_src &&
                                      copy_src <= Zlength(source_words) &&
                                      binary_watch_copy_progress(
                                        watch_memory, raw_prefix, scan_current,
                                        raw_suffix, ii, jj, copy_src, copy_dst,
                                        copy_memory) &&
                                      logical_words == app(retained, rest) &&
                                      ms_wm(Mscan) ==
                                        app(scan_wm_pre,
                                            cons(logical_words,
                                                 scan_wm_post)) &&
                                      ms_wcaps(Mscan) ==
                                        app(scan_caps_pre,
                                            cons(scan_wcap, scan_caps_post)) &&
                                      Zlength(scan_wm_pre) == p &&
                                      Zlength(scan_caps_pre) == p &&
                                      ws == vecp_slot(wlists_entry, p) &&
                                      propagation_capacity_target_facts(
                                        Mscan, wlists_entry, destination, candidate,
                                        scan_wm_pre, scan_wm_post,
                                        scan_caps_pre, scan_caps_post) &&
                                      propagation_scan_candidate_layout(
                                        scan_current, lits, stop, k, offset,
                                        false_lit, p, candidate, sig,
                                        clause_contents) &&
                                      watch0 + false_lit == Znth(0, clause_contents, 0) + Znth(1, clause_contents, 0) &&
                                      0 <= Zlength(source_words) &&
                                      Zlength(source_words) <= scan_wcap &&
                                      0 < scan_wcap &&
                                      scan_wcap <= INT_MAX &&
                                      vecp_rep(
                                        destination,
                                        wlists_split_target_words(
                                          Zlength(scan_wm_pre),
                                          lit_neg_c(candidate), scan_wm_pre,
                                          scan_wm_post),
                                        wlists_split_target_cap(
                                          Zlength(scan_wm_pre),
                                          lit_neg_c(candidate), scan_caps_pre,
                                          scan_caps_post)) *
                                      solver_wlists_handle(s, wlists_entry) *
                                      wlists_split_except_two(
                                        wlists_entry, Zlength(scan_wm_pre),
                                        lit_neg_c(candidate), scan_wm_pre,
                                        scan_wm_post, scan_caps_pre,
                                        scan_caps_post) *
                                      clause_db_pair_frame(
                                        ms_prob(Mscan), ms_learnt(Mscan),
                                        scan_current, clause_contents) *
                                      store(lits + 0 * sizeof(int), int,
                                            watch0) *
                                      store(lits + 1 * sizeof(int), int,
                                            false_lit) *
                                      store(k, int, candidate) *
                                      IntArray::missing_i(
                                        lits, offset, 2,
                                        Zlength(clause_contents),
                                        sublist(2, Zlength(clause_contents),
                                                clause_contents)) *
                                      store(&(ws->size), int,
                                            Zlength(source_words)) *
                                      store(&(ws->cap), int, scan_wcap) *
                                      store(&(ws->ptr), void **, begin) *
                                      PtrArray::full(
                                        begin, Zlength(source_words),
                                        copy_memory) *
                                      PtrArray::undef_seg(
                                        begin, Zlength(source_words),
                                        scan_wcap) *
                                      store(&(s->qhead), int,
                                            mt_qhead(ms_core(Mscan))) *
                                      store(&(s->levels), int *, levels_entry) *
                                      solver_propagation_scan_arrays_noqh_at(
                                        s, Mscan, values, s->reasons, levels_entry,
                                        s->trail, simp_count, prop_count) *
                                      data_at(conflict_out, 0) *
                                      has_permission(&#sig)
                                 */
                                while (i < endvar) {
                                    /*@ Given copy_memory copy_src copy_dst */
                                    /*@ i == begin + copy_src &&
                                          j == begin + copy_dst &&
                                          0 <= copy_dst &&
                                          copy_dst <= copy_src &&
                                          copy_src < Zlength(source_words) &&
                                          PtrArray::full(
                                            begin, Zlength(source_words),
                                            copy_memory)
                                        which implies
                                        ((copy_dst == copy_src &&
                                          i == begin + copy_src &&
                                          j == begin + copy_dst &&
                                          data_at(
                                            i, Znth(copy_src,
                                              copy_memory, 0)) *
                                          PtrArray::missing_i(
                                            begin, copy_src, 0,
                                            Zlength(source_words),
                                            copy_memory)) ||
                                         (copy_dst < copy_src &&
                                          i == begin + copy_src &&
                                          j == begin + copy_dst &&
                                          PtrArray::seg(
                                            begin, 0, copy_dst,
                                            sublist(0, copy_dst,
                                              copy_memory)) *
                                          data_at(
                                            j, Znth(copy_dst,
                                              copy_memory, 0)) *
                                          PtrArray::seg(
                                            begin, copy_dst + 1,
                                            copy_src,
                                            sublist(copy_dst + 1,
                                              copy_src,
                                              copy_memory)) *
                                          data_at(
                                            i, Znth(copy_src,
                                              copy_memory, 0)) *
                                          PtrArray::seg(
                                            begin, copy_src + 1,
                                            Zlength(source_words),
                                            sublist(copy_src + 1,
                                              Zlength(source_words),
                                              copy_memory))))
                                     */
                                    *j = *i;
                                    j++;
                                    i++;
                                }
                                /*@ Given copy_memory copy_src copy_dst */
                                /*@
                                      i >= endvar &&
                                      endvar == begin + Zlength(source_words) &&
                                      i == begin + copy_src &&
                                      j == begin + copy_dst &&
                                      0 <= copy_dst &&
                                      copy_dst <= copy_src &&
                                      copy_src <= Zlength(source_words) &&
                                      binary_watch_copy_progress(
                                        watch_memory, raw_prefix,
                                        scan_current, raw_suffix,
                                        ii, jj, copy_src, copy_dst,
                                        copy_memory) &&
                                      0 <= Zlength(source_words) &&
                                      Zlength(source_words) <= scan_wcap &&
                                      0 < scan_wcap && scan_wcap <= INT_MAX &&
                                      store(&(ws->size), int,
                                            Zlength(source_words)) *
                                      store(&(ws->cap), int, scan_wcap) *
                                      store(&(ws->ptr), void **, begin) *
                                      PtrArray::full(
                                        begin, Zlength(source_words),
                                        copy_memory) *
                                      PtrArray::undef_seg(
                                        begin, Zlength(source_words), scan_wcap)
                                    which implies
                                    endvar == begin + Zlength(source_words) &&
                                    i >= endvar &&
                                    i == begin + copy_src &&
                                    j == begin + copy_dst &&
                                    0 <= copy_dst &&
                                    copy_dst <= copy_src &&
                                    copy_src <= Zlength(source_words) &&
                                    0 <= j - begin &&
                                    j - begin <= Zlength(copy_memory) &&
                                    vecp_rep(ws, copy_memory, scan_wcap)
                                 */
                                // No `has_permission(&begin)` on this RHS.  The block is
                                // PARTIAL, so the `begin` cell is FRAMED through it; adding
                                // has_permission demands a SECOND cell at the same address
                                // and the next call reports `dup_data_at_error(begin_addr)`.
                                // (Value mentions of `begin` do not create a cell, so
                                // nothing is lost by dropping it.)
                                vecp_resize(ws, (int)(j - begin));
                                s->qhead--;
                                *conflict_out = (clause *)0;
                                // `copy_memory` / `copy_dst` are already live from the
                                // post-loop `Given` run above; re-declaring a live name
                                // is a fatal duplicate.
                                /*@ propagation_scan_open(
                                      n, F, A_arr, K, M0, Mentry, Mscan, p,
                                      confl, source_words, retained, moved,
                                      rest, garbage, watch_memory, ii, jj,
                                      scan_current, raw_suffix) &&
                                    minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
                                    binary_watch_copy_progress(
                                      watch_memory, raw_prefix, scan_current,
                                      raw_suffix, ii, jj, copy_src, copy_dst,
                                      copy_memory) &&
                                    endvar == begin + Zlength(source_words) && i >= endvar &&
                                    i == begin + copy_src &&
                                    j == begin + copy_dst &&
                                    0 <= copy_dst && copy_dst <= copy_src &&
                                    copy_src <= Zlength(source_words) &&
                                    propagation_scan_slot(
                                      Mscan, p, scan_wm_pre, logical_words,
                                      scan_wm_post, scan_caps_pre, scan_wcap,
                                      scan_caps_post) &&
                                    ws == vecp_slot(wlists_entry, p) &&
                                    propagation_capacity_target_facts(
                                      Mscan, wlists_entry, destination, candidate,
                                      scan_wm_pre, scan_wm_post,
                                      scan_caps_pre, scan_caps_post) &&
                                    propagation_scan_candidate_layout(
                                      scan_current, lits, stop, k, offset,
                                      false_lit, p, candidate, sig,
                                      clause_contents) &&
                                    watch0 + false_lit == Znth(0, clause_contents, 0) + Znth(1, clause_contents, 0) &&
                                    solver_wlists_handle(s, wlists_entry) *
                                    wlists_split_except_two(
                                      wlists_entry, Zlength(scan_wm_pre),
                                      lit_neg_c(candidate), scan_wm_pre,
                                      scan_wm_post, scan_caps_pre,
                                      scan_caps_post) *
                                    clause_db_pair_frame(
                                      ms_prob(Mscan), ms_learnt(Mscan),
                                      scan_current, clause_contents) *
                                    store(lits + 0 * sizeof(int), int, watch0) *
                                    store(lits + 1 * sizeof(int), int, false_lit) *
                                    store(k, int, candidate) *
                                    IntArray::missing_i(
                                      lits, offset, 2, Zlength(clause_contents),
                                      sublist(2, Zlength(clause_contents),
                                              clause_contents)) *
                                    store(&(s->qhead), int, mt_qhead(ms_core(Mscan)) - 1) *
                                    store(&(s->levels), int *, levels_entry) *
                                    solver_propagation_scan_arrays_noqh_at(
                                      s, Mscan, values, s->reasons, levels_entry,
                                      s->trail, simp_count, prop_count) *
                                    data_at(conflict_out, 0)
                                    which implies
                                    exists prob_after learnt_after M_after,
                                      db_pair_lits_update(
                                        ms_prob(Mscan), ms_learnt(Mscan),
                                        scan_current, clause_contents,
                                        propagation_normalized_clause(
                                          watch0, false_lit, clause_contents),
                                        prob_after, learnt_after) &&
                                      propagation_capacity_abort_state(
                                        n, F, A_arr, K, Mscan, prob_after,
                                        learnt_after,
                                        app(scan_wm_pre,
                                          cons(sublist(0, j - begin, copy_memory),
                                               scan_wm_post)),
                                        app(scan_caps_pre,
                                          cons(scan_wcap, scan_caps_post)),
                                        simp_count, prop_count, M_after) &&
                                      minisat_propagation_reuse_live(M0, M_after) &&
                                      confl == 0 &&
                                      Zlength(scan_wm_pre) == p &&
                                      ws == vecp_slot(wlists_entry, p) &&
                                      endvar == begin + Zlength(source_words) &&
                                      i >= endvar &&
                                      j == begin + copy_dst &&
                                      0 <= copy_dst &&
                                      copy_dst <= Zlength(source_words) &&
                                      propagation_scan_candidate_layout(
                                        scan_current, lits, stop, k, offset,
                                        false_lit, p, candidate, sig,
                                        clause_contents) &&
                                      destination == vecp_slot( wlists_entry, lit_neg_c(candidate)) &&
                                      propagation_capacity_physical_alias(
                                        wlists_entry, Zlength(scan_wm_pre),
                                        lit_neg_c(candidate), ws, destination,
                                        scan_wm_pre, scan_wm_post,
                                        scan_caps_pre, scan_caps_post,
                                        wlists_split_target_words(Zlength(scan_wm_pre),
                                          lit_neg_c(candidate), scan_wm_pre,
                                          scan_wm_post),
                                        wlists_split_target_cap(Zlength(scan_wm_pre),
                                          lit_neg_c(candidate), scan_caps_pre,
                                          scan_caps_post)) &&
                                      solver_propagation_capacity_rest_at(
                                        s, M_after, wlists_entry, Zlength(scan_wm_pre),
                                        lit_neg_c(candidate), scan_wm_pre,
                                        scan_wm_post, scan_caps_pre,
                                        scan_caps_post, values, levels_entry) *
                                      data_at(conflict_out, 0)
                                 */
                                // No `has_permission(&lits)` on this RHS: PARTIAL block, so
                                // the `lits` cell is framed through and a second one here is
                                // reported as `dup_data_at_error(lits_addr)`.
                                /*@ Given M_after */
                                // `destination_base` is an LHS EXISTENTIAL, not the local
                                // `destination`, and it carries NO pure equation.  At this
                                // point, the copy loop's
                                // `Inv Assert` re-bound every local to a fresh value, so the
                                // frame holds
                                //   vecp_rep(destination_4652_value, target_words, target_cap)
                                // while the local's CELL was canonicalised by the invariant's
                                // own `destination == vecp_slot(wlists_entry, lit_neg_c(candidate))`
                                // conjunct to
                                //   store(destination_addr, vecp_slot(wlists_entry, lit_neg_c(candidate)))
                                // and the two are related only by a PROP equation.  Naming
                                // `destination` here therefore demands
                                // `vecp_rep(vecp_slot(...), ...)`, which is a DIFFERENT atom
                                // -- QCP has no congruence closure in predicate-argument
                                // position (`ws`'s vector escapes this because it sits in the
                                // frame as raw cells, and ADDRESS positions are matched up to
                                // equality).  Binding the pointer spatially instead makes the
                                // match syntactic.  The link the Coq wit needs is supplied by
                                // `propagation_capacity_physical_alias`, whose whole purpose
                                // is to let symexec infer the physical
                                // witnesses from the spatial atoms FIRST and recover
                                // `destination_ptr = vecp_slot wlists_entry target` by inversion; that
                                // is also why no `destination_base == ...` equation is
                                // written -- a defining equation would be solved BEFORE the
                                // spatial match and re-open the mismatch.
                                // The two `j - begin` / `ws == vecp_slot(wlists_entry, p)` conjuncts are
                                // written on BOTH sides on purpose.  A value mention of
                                // a C local on a
                                // `which implies` LHS CONSUMES that local's cell, and a value
                                // mention on the RHS materialises it.  This LHS names `j`,
                                // `begin` (via `j - begin`), `ws` and `p`; an RHS naming
                                // none of them would destroy all four cells and the
                                // `return` would report `Fail to Remove Memory Permission of j`.
                                // `s` and `values` survive because the RHS's
                                // `solver_propagation_capacity_raw(s, ..., values, ...)`
                                // names them.  Both restated facts are ambient (the
                                // `j - begin` bound is the previous scan-exit block's own
                                // RHS; `ws == vecp_slot(wlists_entry, p)` is on the loop invariant), so
                                // the LHS discharges at symexec time and the RHS half of the
                                // wit is the LHS conjunct verbatim.
                                /*@ exists destination_base,
                                      0 <= j - begin &&
                                      j - begin <= Zlength(copy_memory) &&
                                      ws == vecp_slot(wlists_entry, p) &&
                                      propagation_caller_frame(M0, M_after) &&
                                      solver_propagation_inv(n, F, A_arr, K, M_after) &&
                                      minisat_propagation_reuse_live(M0, M_after) &&
                                      msolver_seed_shadow(M_after) &&
                                      solver_capacity_exhausted(M_after) &&
                                      solver_watch_capacity_exhausted(M_after) &&
                                      mt_qhead(ms_core(M_after)) < ms_qtail(M_after) &&
                                      solver_shape(M_after) &&
                                      ms_wm(M_after) == app(
                                        scan_wm_pre,
                                        cons(sublist(0, j - begin, copy_memory),
                                             scan_wm_post)) &&
                                      ms_wcaps(M_after) == app(
                                        scan_caps_pre,
                                        cons(scan_wcap, scan_caps_post)) &&
                                      Zlength(scan_wm_pre) == p &&
                                      Zlength(scan_caps_pre) == p &&
                                      propagation_destination_index(
                                        2 * ms_size(M_after), p,
                                        lit_neg_c(candidate)) &&
                                      propagation_capacity_physical_alias(
                                        wlists_entry, p, lit_neg_c(candidate), ws,
                                        destination_base, scan_wm_pre,
                                        scan_wm_post,
                                        scan_caps_pre, scan_caps_post,
                                        wlists_split_target_words(
                                          p, lit_neg_c(candidate),
                                          scan_wm_pre, scan_wm_post),
                                        wlists_split_target_cap(
                                          p, lit_neg_c(candidate),
                                          scan_caps_pre, scan_caps_post)) &&
                                      solver_propagation_capacity_rest_at(
                                        s, M_after, wlists_entry, Zlength(scan_wm_pre),
                                        lit_neg_c(candidate), scan_wm_pre,
                                        scan_wm_post, scan_caps_pre,
                                        scan_caps_post, values,
                                        levels_entry) *
                                      vecp_rep(
                                        ws, sublist(0, j - begin, copy_memory),
                                        scan_wcap) *
                                      vecp_rep(
                                        destination_base,
                                        wlists_split_target_words(
                                          Zlength(scan_wm_pre),
                                          lit_neg_c(candidate),
                                          scan_wm_pre, scan_wm_post),
                                        wlists_split_target_cap(
                                          Zlength(scan_wm_pre),
                                          lit_neg_c(candidate),
                                          scan_caps_pre, scan_caps_post)) *
                                      data_at(conflict_out, 0)
                                    which implies
                                      0 <= j - begin &&
                                      j - begin <= Zlength(copy_memory) &&
                                      ws == vecp_slot(wlists_entry, p) &&
                                      solver_propagation_capacity_raw(
                                        s, n, F, A_arr, K, M0,
                                        values, levels_entry, wlists_entry) *
                                      data_at(conflict_out, 0)
                                 */
                                return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
                            }
                            /*@ exists destination_ptr destination_cap_now,
                                  wlists_split_target_cap(
                                    Zlength(scan_wm_pre),
                                    lit_neg_c(candidate),
                                    scan_caps_pre, scan_caps_post) <= destination_cap_now &&
                                  destination_cap_now <= INT_MAX &&
                                  Zlength(wlists_split_target_words(
                                    Zlength(scan_wm_pre),
                                    lit_neg_c(candidate),
                                    scan_wm_pre, scan_wm_post)) < destination_cap_now &&
                                  store(&(destination->size), int,
                                    Zlength(wlists_split_target_words(
                                      Zlength(scan_wm_pre),
                                      lit_neg_c(candidate),
                                      scan_wm_pre, scan_wm_post))) *
                                  store(&(destination->cap), int,
                                        destination_cap_now) *
                                  store(&(destination->ptr), void **,
                                        destination_ptr) *
                                  PtrArray::seg(destination_ptr, 0,
                                    Zlength(wlists_split_target_words(
                                      Zlength(scan_wm_pre),
                                      lit_neg_c(candidate),
                                      scan_wm_pre, scan_wm_post)),
                                    wlists_split_target_words(
                                      Zlength(scan_wm_pre),
                                      lit_neg_c(candidate),
                                      scan_wm_pre, scan_wm_post)) *
                                  PtrArray::undef_seg(destination_ptr,
                                    Zlength(wlists_split_target_words(
                                      Zlength(scan_wm_pre),
                                      lit_neg_c(candidate),
                                      scan_wm_pre, scan_wm_post)),
                                    destination_cap_now)
                                which implies
                                exists destination_cap,
                                  wlists_split_target_cap(
                                    Zlength(scan_wm_pre),
                                    lit_neg_c(candidate),
                                    scan_caps_pre, scan_caps_post) <= destination_cap &&
                                  destination_cap <= INT_MAX &&
                                  Zlength(
                                    wlists_split_target_words(
                                      Zlength(scan_wm_pre),
                                      lit_neg_c(candidate),
                                      scan_wm_pre, scan_wm_post)) < destination_cap &&
                                  vecp_rep(
                                    destination,
                                    wlists_split_target_words(
                                      Zlength(scan_wm_pre),
                                      lit_neg_c(candidate),
                                      scan_wm_pre, scan_wm_post),
                                    destination_cap)
                             */
                            /*@ Given destination_cap */
                            lits[1] = *k;
                            *k = false_lit;
                            /*@ i == begin + ii &&
                                  0 <= ii &&
                                  ii < Zlength(source_words) &&
                                  Znth(ii, candidate_post_memory, 0) ==
                                    scan_current &&
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    candidate_post_memory)
                                which implies
                                Znth(
                                  ii, candidate_post_memory, 0) ==
                                  scan_current &&
                                data_at(
                                  i,
                                  Znth(
                                    ii, candidate_post_memory, 0)) *
                                PtrArray::missing_i(
                                  begin, ii, 0,
                                  Zlength(source_words),
                                  candidate_post_memory)
                             */
                            check(vecp_push(destination, *i) /*@ where
                                            l =
                                              wlists_split_target_words(
                                                Zlength(scan_wm_pre),
                                                lit_neg_c(candidate),
                                                scan_wm_pre, scan_wm_post),
                                            cap = destination_cap */
                            == 1);
                            // The `data_at(i, ...) * PtrArray::missing_i(...)` focus opened
                            // just above does NOT survive the `vecp_push` call: strategy rule
                            // 27 has `priority : post(5)`, so it fires on the state after the
                            // call, matching `PtrArray::missing_i(begin, ii, 0, ...)` against
                            // `store(pointer_offset(begin, ii, PTR), PTR, ...)` (its three
                            // `infer` checks `0 <= ii`, `ii < Zlength(source_words)`,
                            // `ii == ii` are all ambient here) and closing the pair itself.
                            // The state right after the call is:
                            //   PtrArray.full(begin, Zlength(source_words),
                            //     replace_Znth(ii, Znth(ii, candidate_post_memory, 0),
                            //                  candidate_post_memory))
                            //   store(i_addr, pointer_offset(begin, ii, PTR), clause**)
                            // i.e. exactly this block's intended RHS, already assembled.  So
                            // the LHS is written in the CLOSED form and this block only names
                            // the result.  The RHS carries no `store(&i, clause **, i)`: the
                            // LHS no longer names `i` as a value, so `i`'s cell stays framed
                            // and re-emitting it would be a duplicate.  The sibling focuses
                            // that straddle the `enqueue` call do not need this treatment;
                            // they pass as written.
                            // The extra RHS conjunct `Znth(ii, migration_post_memory, 0) ==
                            // scan_current` is what the destination-vector block below needs.
                            // `vecp_push` pushed the value it read out of `*i`, and rule 27's
                            // write-close re-spelled that value to
                            // `Znth(ii, replace_Znth(ii, Znth(ii, cpm, 0), cpm), 0)`,
                            // so the vector's contents no longer mention
                            // `scan_current` at all.  Proving the equation HERE is cheap --
                            // this LHS has `Znth(ii, candidate_post_memory, 0) ==
                            // scan_current`, `0 <= ii < Zlength(source_words)`, and the
                            // `PtrArray::full` that fixes `Zlength(candidate_post_memory) ==
                            // Zlength(source_words)` -- whereas the block below has no source
                            // for any of them.
                            /*@ Znth(ii, candidate_post_memory, 0) == scan_current &&
                                  0 <= ii &&
                                  ii < Zlength(source_words) &&
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    replace_Znth(
                                      ii,
                                      Znth(
                                        ii,
                                        candidate_post_memory, 0),
                                      candidate_post_memory))
                                which implies
                                exists migration_post_memory,
                                  migration_post_memory ==
                                    replace_Znth(
                                      ii,
                                      Znth(
                                        ii,
                                        candidate_post_memory, 0),
                                      candidate_post_memory) &&
                                  Znth(ii, migration_post_memory, 0) ==
                                    scan_current &&
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    migration_post_memory)
                             */
                            /*@ Given migration_post_memory */
                            // The vector's last element is spelled
                            // `Znth(ii, migration_post_memory, 0)` on the LHS, not
                            // `scan_current`: that is the spelling the state carries after
                            // rule 27's write-close (`migration_post_memory` canonicalises to
                            // `replace_Znth(ii, Znth(ii, cpm, 0), cpm)`, which is exactly the
                            // term the state carries).  The equation restated on this LHS is the one
                            // proved by the block above, and it is what lets the wit re-spell
                            // the RHS back to `scan_current` for the downstream consumers.
                            /*@ destination ==
                                    vecp_slot(wlists_entry, lit_neg_c(candidate)) &&
                                  Znth(ii, migration_post_memory, 0) ==
                                    scan_current &&
                                  vecp_rep(
                                    destination,
                                    app(wlists_split_target_words(
                                          Zlength(scan_wm_pre),
                                          lit_neg_c(candidate),
                                          scan_wm_pre, scan_wm_post),
                                        cons(migration_post_memory[ii],
                                             nil)),
                                    destination_cap)
                                which implies exists destination_index,
                                  propagation_real_migrated_physical_alias(
                                    wlists_entry, Zlength(scan_wm_pre),
                                    lit_neg_c(candidate), scan_current,
                                    destination_index,
                                    vecp_slot(wlists_entry, lit_neg_c(candidate)),
                                    scan_wm_pre, scan_wm_post,
                                    app(wlists_split_target_words(
                                          Zlength(scan_wm_pre),
                                          lit_neg_c(candidate),
                                          scan_wm_pre, scan_wm_post),
                                        cons(scan_current, nil))) &&
                                  store(&destination, vecp *,
                                    vecp_slot(wlists_entry, lit_neg_c(candidate))) *
                                  vecp_rep(
                                    vecp_slot(wlists_entry, lit_neg_c(candidate)),
                                    app(wlists_split_target_words(
                                          Zlength(scan_wm_pre),
                                          lit_neg_c(candidate),
                                          scan_wm_pre, scan_wm_post),
                                        cons(scan_current, nil)),
                                    destination_cap)
                             */
                            // Open the destination vector while its cap witness is still a
                            // live Given.  The raw pointer/cap cells survive the loop exit,
                            // so the tagged transition can bind both witnesses spatially.
                            /*@ exists destination_index destination_ptr,
                                exists destination_words destination_cap_open,
                                  propagation_real_migrated_physical_alias(
                                    wlists_entry, Zlength(scan_wm_pre), lit_neg_c(candidate),
                                    scan_current, destination_index, destination_ptr,
                                    scan_wm_pre, scan_wm_post, destination_words) &&
                                  vecp_rep(destination_ptr, destination_words,
                                    destination_cap_open)
                                which implies exists destination_base,
                                  propagation_real_migrated_physical_alias(
                                    wlists_entry, Zlength(scan_wm_pre), lit_neg_c(candidate),
                                    scan_current, destination_index, destination_ptr,
                                    scan_wm_pre, scan_wm_post, destination_words) &&
                                  0 <= Zlength(destination_words) &&
                                  Zlength(destination_words) <= destination_cap_open &&
                                  0 < destination_cap_open &&
                                  destination_cap_open <= INT_MAX &&
                                  store(vecp_size_addr(destination_ptr), int,
                                    Zlength(destination_words)) *
                                  store(vecp_cap_addr(destination_ptr),
                                    int, destination_cap_open) *
                                  store(vecp_ptr_addr(destination_ptr),
                                    void **, destination_base) *
                                  PtrArray::full(destination_base,
                                    Zlength(destination_words), destination_words) *
                                  PtrArray::undef_seg(destination_base,
                                    Zlength(destination_words),
                                    destination_cap_open)
                             */
                            /*@ Given destination_base */
                            break;
                        }
                        // Bumping
                        // `propagation_replacement_scan_inv` from `offset` to `offset + 1`
                        // needs `offset + 1 <= Zlength words`, and the LHS instance only
                        // gives `offset <= Zlength words`.  The missing fact is the `for`
                        // condition `k < stop` (with `k == lits + offset`,
                        // `stop == lits + Zlength(clause_contents)`), which is ambient only.
                        // `3 <= Zlength(clause_contents)` is what makes
                        // `Zlength(propagation_normalized_clause(...)) ==
                        //  Zlength(clause_contents)`, so the bound transfers to `words`.
                        // Both are already written on this loop's own `Inv Assert` and on
                        // the capacity-abort bridge inside the same body,
                        // so both are derivable here.
                        /*@ propagation_replacement_scan_inv(
                              n, Mscan, false_lit,
                              propagation_normalized_clause(
                                watch0, false_lit, clause_contents),
                              offset) &&
                              3 <= Zlength(clause_contents) &&
                              offset < Zlength(clause_contents) &&
                              candidate == Znth(
                                offset,
                                propagation_normalized_clause(
                                  watch0, false_lit, clause_contents), 0) &&
                              sig == 2 * lit_sign_c(candidate) - 1 &&
                              Znth(lit_var_c(candidate),
                                mt_assigns(ms_core(Mscan)), 0) == sig
                            which implies
                                propagation_replacement_scan_inv(
                                  n, Mscan, false_lit,
                                  propagation_normalized_clause(
                                  watch0, false_lit, clause_contents),
                                  offset + 1) &&
                              has_permission(&sig)
                         */
                    }

                    // Only the replacement loop's OWN `Inv Assert` existentials are
                    // re-declared here: they died with the loop body, and QCP does not
                    // put them back automatically ("Use of undeclared identifier" otherwise).
                    // ii / jj / candidate_post_memory / raw_prefix / raw_suffix are still
                    // live from the enclosing scopes, and re-declaring a live name is a
                    // fatal duplicate.
                    /*@ Given watch0 offset */
                    if (k == stop){
                        /*@ propagation_replacement_scan_inv(
                              n, Mscan, false_lit,
                              propagation_normalized_clause(
                                watch0, false_lit, clause_contents),
                              offset) &&
                              k == lits + offset && k == stop &&
                              stop == lits + Zlength(clause_contents) &&
                              3 <= Zlength(clause_contents)
                            which implies
                              k == lits + offset && k == stop &&
                              stop == lits + Zlength(clause_contents) &&
                              propagation_replacement_scan_inv(
                                n, Mscan, false_lit,
                                propagation_normalized_clause(
                                  watch0, false_lit, clause_contents),
                                Zlength(clause_contents))
                         */
                        /*@ i == begin + ii &&
                              j == begin + jj &&
                              0 <= jj && jj <= ii &&
                              0 <= ii &&
                              ii < Zlength(source_words) &&
                              PtrArray::full(
                                begin, Zlength(source_words),
                                candidate_post_memory)
                            which implies
                            ((jj == ii &&
                              i == begin + ii &&
                              j == begin + jj &&
                              j == i &&
                              propagation_ptr_segment(
                                begin, 0, ii,
                                sublist(
                                  0, ii,
                                  candidate_post_memory)) *
                              data_at(
                                begin + ii * sizeof(struct clause_t *),
                                struct clause_t *,
                                Znth(
                                  ii,
                                  candidate_post_memory, 0)) *
                              propagation_ptr_segment(
                                begin, ii + 1,
                                Zlength(source_words),
                                sublist(ii + 1,
                                  Zlength(source_words),
                                  candidate_post_memory))) ||
                             (jj < ii &&
                              i == begin + ii &&
                              j == begin + jj &&
                              propagation_ptr_segment(
                                begin, 0, jj,
                                sublist(
                                  0, jj,
                                  candidate_post_memory)) *
                              data_at(
                                begin + jj * sizeof(struct clause_t *),
                                struct clause_t *,
                                Znth(
                                  jj,
                                  candidate_post_memory, 0)) *
                              propagation_ptr_segment(
                                begin, jj + 1, ii,
                                sublist(jj + 1, ii,
                                  candidate_post_memory)) *
                              data_at(
                                begin + ii * sizeof(struct clause_t *),
                                struct clause_t *,
                                Znth(
                                  ii,
                                  candidate_post_memory, 0)) *
                              propagation_ptr_segment(
                                begin, ii + 1,
                                Zlength(source_words),
                                sublist(ii + 1,
                                  Zlength(source_words),
                                  candidate_post_memory))))
                            $ unit_same unit_move
                         */
                        *j = *i;
                        j++;
                        // Clause is unit under assignment:
                        /*@ exists rsn trl,
                              enqueue_input(
                                ms_size(Mscan), watch0, ms_qtail(Mscan),
                                mt_assigns(ms_core(Mscan)),
                                mt_levels(ms_core(Mscan)),
                                ms_reason_words(Mscan),
                                mt_trail(ms_core(Mscan))) &&
                              0 <= ms_size(Mscan) &&
                              ms_size(Mscan) <= ms_cap(Mscan) &&
                              ms_cap(Mscan) <= INT_MAX &&
                              ms_qtail(Mscan) <= ms_cap(Mscan) &&
                              store(&(s->levels), int *, levels_entry) *
                              store(&(s->reasons), clause **, rsn) *
                              store(&(s->trail), lit *, trl) *
                              CharArray::seg(
                                values, 0, ms_size(Mscan),
                                mt_assigns(ms_core(Mscan))) *
                              CharArray::undef_seg(
                                values, ms_size(Mscan), ms_cap(Mscan)) *
                              solver_propagation_scan_core_at(
                                s, Mscan, values, rsn, levels_entry, trl,
                                simp_count, prop_count)
                            which implies
                            enqueue_input(
                              ms_size(Mscan), watch0, ms_qtail(Mscan),
                              mt_assigns(ms_core(Mscan)),
                              mt_levels(ms_core(Mscan)),
                              ms_reason_words(Mscan),
                              mt_trail(ms_core(Mscan))) &&
                            enqueue_state_at(
                              s, values, levels_entry,
                              ms_size(Mscan), ms_cap(Mscan), ms_qtail(Mscan),
                              mt_assigns(ms_core(Mscan)),
                              mt_levels(ms_core(Mscan)),
                              ms_reason_words(Mscan),
                              mt_trail(ms_core(Mscan)),
                              mt_lim(ms_core(Mscan)), ms_lim_cap(Mscan)) *
                            store(&(s->simpdb_props), int, simp_count) *
                            store(&(s->binary), clause *, ms_binary(Mscan)) *
                            solver_binary_rep(Mscan) *
                            store(&(s->stats.propagations), unsigned long long,
                                  prop_count) *
                            store(&(s->stats.inspects), unsigned long long,
                                  stats_inspects(ms_stats(Mscan))) *
                            solver_propagate_frame(s, Mscan)
                         */
                        if (!enqueue(s,lits[0], *i)){
                            confl = *i;
                            /*@ exists conflict_ret,
                                  conflict_ret <= 0 &&
                                  solver_shape(Mscan) &&
                                  msolver_seed_shadow(Mscan) &&
                                  propagation_caller_frame(M0, Mscan) &&
                                  propagation_scan_frontier(
                                    Mentry, Mscan, p) &&
                                  solver_propagation_scan_semantics(
                                    n, F, A_arr, K, Mscan, p, 0,
                                    retained, rest) &&
                                  minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                                  propagation_replacement_scan_inv(
                                    n, Mscan, false_lit,
                                    propagation_normalized_clause(
                                      watch0, false_lit,
                                      clause_contents),
                                    Zlength(
                                      propagation_normalized_clause(
                                        watch0, false_lit,
                                        clause_contents))) &&
                                  rest == cons(scan_current, raw_suffix) &&
                                  confl == scan_current &&
                                  Znth(ii, candidate_post_memory, 0) ==
                                    scan_current &&
                                  false_lit == lit_neg_c(p) &&
                                  clause_lits_pointer(
                                    scan_current, lits) &&
                                  real_watch_pair(
                                    Zlength(scan_wm_pre), clause_contents) &&
                                  Zlength(scan_wm_pre) == p &&
                                  watch0 + false_lit ==
                                    Znth(0, clause_contents, 0) +
                                    Znth(1, clause_contents, 0) &&
                                  simp_count ==
                                    ms_simpdb_props(Mscan) &&
                                  prop_count ==
                                    stats_propagations(ms_stats(Mscan)) &&
                                  clause_db_pair_frame(
                                    ms_prob(Mscan), ms_learnt(Mscan),
                                    scan_current, clause_contents) *
                                  store(lits + 0 * sizeof(int), int,
                                        watch0) *
                                  store(lits + 1 * sizeof(int), int,
                                        false_lit) *
                                  IntArray::seg(
                                    lits, 2, Zlength(clause_contents),
                                    sublist(2, Zlength(clause_contents),
                                            clause_contents)) *
                                  enqueue_post_at(
                                    s, values, levels_entry,
                                    watch0,
                                    Znth(ii, candidate_post_memory, 0),
                                    ms_size(Mscan), ms_cap(Mscan),
                                    ms_qtail(Mscan), conflict_ret,
                                    mt_assigns(ms_core(Mscan)),
                                    mt_levels(ms_core(Mscan)),
                                    ms_reason_words(Mscan),
                                    mt_trail(ms_core(Mscan)),
                                    mt_lim(ms_core(Mscan)),
                                    ms_lim_cap(Mscan)) *
                                  store(&(s->qhead), int,
                                    mt_qhead(ms_core(Mscan))) *
                                  store(&(s->simpdb_props), int,
                                    simp_count) *
                                  store(&(s->binary), clause *,
                                    ms_binary(Mscan)) *
                                  solver_binary_rep(Mscan) *
                                  store(&(s->stats.propagations),
                                    unsigned long long, prop_count) *
                                  store(&(s->stats.inspects),
                                    unsigned long long,
                                    stats_inspects(ms_stats(Mscan))) *
                                  solver_propagate_frame(s, Mscan)
                                which implies
                                exists prob_route learnt_route Mroute,
                                  propagation_unit_conflict_ready(
                                    n, F, A_arr, K, Mscan, p,
                                    scan_current, watch0, false_lit,
                                    clause_contents, retained, rest,
                                    prob_route, learnt_route, Mroute) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, scan_current, nil) &&
                                  solver_shape(Mroute) &&
                                  msolver_seed_shadow(Mroute) &&
                                  propagation_caller_frame(M0, Mroute) &&
                                  propagation_scan_frontier( Mentry, Mroute, p) &&
                                  ms_wm(Mroute) == ms_wm(Mscan) &&
                                  ms_wcaps(Mroute) == ms_wcaps(Mscan) &&
                                  simp_count ==
                                    ms_simpdb_props(Mroute) &&
                                  prop_count ==
                                    stats_propagations(ms_stats(Mroute)) &&
                                  confl == scan_current &&
                                  clause_db_rep(prob_route) *
                                  clause_db_rep(learnt_route) *
                                  solver_propagation_nonwatch_rest_at(
                                    s, Mroute, values, levels_entry) *
                                  has_permission(&lits)
                             */
                            /*@ Given prob_route learnt_route Mroute */
                            i++;
                            // Copy the remaining watches:
                            /*@ ii <= jj && jj <= ii &&
                                Zlength(candidate_post_memory) ==
                                  Zlength(source_words) &&
                                Znth(ii, candidate_post_memory, 0) ==
                                  scan_current &&
                                propagation_ptr_segment(
                                  begin, 0, ii,
                                  sublist(
                                    0, ii,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + ii * sizeof(struct clause_t *),
                                  struct clause_t *,
                                  Znth(ii, candidate_post_memory, 0)) *
                                propagation_ptr_segment(
                                  begin, ii + 1,
                                  Zlength(source_words),
                                  sublist(ii + 1,
                                    Zlength(source_words),
                                    candidate_post_memory))
                                $ unit_same
                                which implies
                                PtrArray::full(
                                  begin, Zlength(source_words),
                                  replace_Znth(
                                    jj, scan_current,
                                    candidate_post_memory))
                                $ unit_same
                             */
                            /*@ Znth(ii, candidate_post_memory, 0) ==
                                  scan_current &&
                                Zlength(candidate_post_memory) ==
                                  Zlength(source_words) &&
                                propagation_ptr_segment(
                                  begin, 0, jj,
                                  sublist(
                                    0, jj,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + jj * sizeof(struct clause_t *),
                                  struct clause_t *,
                                  Znth(ii, candidate_post_memory, 0)) *
                                propagation_ptr_segment(
                                  begin, jj + 1, ii,
                                  sublist(jj + 1, ii,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + ii * sizeof(struct clause_t *),
                                  struct clause_t *,
                                  Znth(ii, candidate_post_memory, 0)) *
                                propagation_ptr_segment(
                                  begin, ii + 1,
                                  Zlength(source_words),
                                  sublist(ii + 1,
                                    Zlength(source_words),
                                    candidate_post_memory))
                                $ unit_move
                                which implies
                                PtrArray::full(
                                  begin, Zlength(source_words),
                                  replace_Znth(
                                    jj, scan_current,
                                    candidate_post_memory))
                                $ unit_move
                             */
                            /* The two paths have different private arithmetic facts but the
                               same semantic copy state.  Give them one group name so the full
                               loop invariant below, rather than a partial join, abstracts those
                               private facts in V2.1.0. */
                            /*@ Branch name
                                unit_conflict_copy: 0 <= jj && jj <= ii
                             */
                            /*@ Inv Assert exists copy_memory copy_src copy_dst,
                                  s == s@pre && conflict_out == conflict_out@pre &&
                                  values == assigns_entry &&
                                  solver_shape(Mroute) &&
                                  msolver_seed_shadow(Mroute) &&
                                  propagation_caller_frame(M0, Mroute) &&
                                  propagation_scan_frontier( Mentry, Mroute, p) &&
                                  propagation_watch_scan_physical(
                                    source_words, retained, moved, rest,
                                    garbage, watch_memory, ii, jj) &&
                                  propagation_unit_conflict_ready(
                                    n, F, A_arr, K, Mscan, p,
                                    scan_current, watch0, false_lit,
                                    clause_contents, retained, rest,
                                    prob_route, learnt_route, Mroute) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, scan_current, nil) &&
                                  rest == cons(scan_current, raw_suffix) &&
                                  confl == scan_current &&
                                  endvar == begin + Zlength(source_words) &&
                                  i == begin + copy_src &&
                                  j == begin + copy_dst &&
                                  0 <= copy_dst && copy_dst <= copy_src &&
                                  copy_src <= Zlength(source_words) &&
                                  binary_watch_copy_progress(
                                    watch_memory, raw_prefix,
                                    scan_current, raw_suffix,
                                    ii, jj, copy_src, copy_dst,
                                    copy_memory) &&
                                  ms_wm(Mroute) ==
                                    app(scan_wm_pre,
                                      cons(app(retained, rest),
                                           scan_wm_post)) &&
                                  ms_wcaps(Mroute) ==
                                    app(scan_caps_pre,
                                      cons(scan_wcap, scan_caps_post)) &&
                                  simp_count ==
                                    ms_simpdb_props(Mroute) &&
                                  prop_count ==
                                    stats_propagations(ms_stats(Mroute)) &&
                                  Zlength(scan_wm_pre) == p &&
                                  Zlength(scan_caps_pre) == p &&
                                  ws == vecp_slot(wlists_entry, p) &&
                                  0 <= Zlength(source_words) &&
                                  Zlength(source_words) <= scan_wcap &&
                                  0 < scan_wcap && scan_wcap <= INT_MAX &&
                                  store(&(ws->size), int,
                                    Zlength(source_words)) *
                                  store(&(ws->cap), int, scan_wcap) *
                                  store(&(ws->ptr), void **, begin) *
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    copy_memory) *
                                  PtrArray::undef_seg(
                                    begin, Zlength(source_words),
                                    scan_wcap) *
                                  wlists_source_hole_handle(
                                    s, wlists_entry, Zlength(scan_wm_pre),
                                    scan_wm_pre, scan_wm_post,
                                    scan_caps_pre, scan_caps_post) *
                                  clause_db_rep(prob_route) *
                                  clause_db_rep(learnt_route) *
                                  solver_propagation_nonwatch_rest_at(
                                    s, Mroute, values, levels_entry) *
                                  data_at(conflict_out, 0) *
                                  has_permission(&sig) *
                                  has_permission(&k) *
                                  has_permission(&lits) *
                                  has_permission(&stop)
                             */
                            while (i < endvar) {
                                /*@ Given copy_memory copy_src copy_dst */
                                /*@ i == begin + copy_src &&
                                      j == begin + copy_dst &&
                                      0 <= copy_dst &&
                                      copy_dst <= copy_src &&
                                      copy_src < Zlength(source_words) &&
                                      PtrArray::full(
                                        begin, Zlength(source_words),
                                        copy_memory)
                                    which implies
                                    ((copy_dst == copy_src &&
                                      i == begin + copy_src &&
                                      j == begin + copy_dst &&
                                      data_at(
                                        i,
                                        Znth(copy_src,
                                             copy_memory, 0)) *
                                      PtrArray::missing_i(
                                        begin, copy_src, 0,
                                        Zlength(source_words),
                                        copy_memory)) ||
                                     (copy_dst < copy_src &&
                                      i == begin + copy_src &&
                                      j == begin + copy_dst &&
                                      PtrArray::seg(
                                        begin, 0, copy_dst,
                                        sublist(0, copy_dst,
                                          copy_memory)) *
                                      data_at(
                                        j,
                                        Znth(copy_dst,
                                             copy_memory, 0)) *
                                      PtrArray::seg(
                                        begin, copy_dst + 1,
                                        copy_src,
                                        sublist(copy_dst + 1,
                                          copy_src, copy_memory)) *
                                      data_at(
                                        i,
                                        Znth(copy_src,
                                             copy_memory, 0)) *
                                      PtrArray::seg(
                                        begin, copy_src + 1,
                                        Zlength(source_words),
                                        sublist(copy_src + 1,
                                          Zlength(source_words),
                                          copy_memory))))
                                 */
                                *j = *i;
                                j++;
                                i++;
                            }
                        /*@ Given copy_memory copy_src copy_dst */
                        /*@ i >= endvar &&
                                  endvar == begin +
                                    Zlength(source_words) &&
                                  i == begin + copy_src &&
                                  j == begin + copy_dst &&
                                  copy_src <=
                                    Zlength(source_words) &&
                                  binary_watch_copy_progress(
                                    watch_memory, raw_prefix,
                                    scan_current, raw_suffix,
                                    ii, jj, copy_src, copy_dst,
                                    copy_memory) &&
                                  propagation_watch_scan_physical(
                                    source_words, retained, moved, rest,
                                    garbage, watch_memory, ii, jj) &&
                                  propagation_unit_conflict_ready(
                                    n, F, A_arr, K, Mscan, p,
                                    scan_current, watch0, false_lit,
                                    clause_contents, retained, rest,
                                    prob_route, learnt_route, Mroute) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, scan_current, nil) &&
                                  confl == scan_current &&
                                  clause_db_rep(prob_route) *
                                  clause_db_rep(learnt_route) *
                                  solver_propagation_nonwatch_rest_at(
                                    s, Mroute, values, levels_entry)
                                which implies
                                exists retained_route garbage_route,
                                  retained_route == app(retained, rest) &&
                                  confl == scan_current &&
                                  i >= endvar &&
                                  endvar == begin + Zlength(source_words) &&
                                  i == begin + copy_src &&
                                  j == begin + copy_dst &&
                                  propagation_unit_conflict_transition(
                                    n, F, A_arr, K, Mscan, p,
                                    scan_current,
                                    prob_route, learnt_route,
                                    retained_route, Mroute) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, scan_current, nil) &&
                                  propagation_scan_conflict_step(
                                    source_words, retained, moved, rest,
                                    copy_memory, garbage_route,
                                    retained_route) &&
                                  solver_propagation_scan_semantics(
                                    n, F, A_arr, K, Mroute, p,
                                    confl, retained_route, nil) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, confl, nil) &&
                                  propagation_watch_scan_physical(
                                    source_words, retained_route,
                                    moved, nil, garbage_route,
                                    copy_memory,
                                    Zlength(source_words),
                                    Zlength(retained_route)) &&
                                  clause_db_rep(prob_route) *
                                  clause_db_rep(learnt_route) *
                                  solver_propagation_nonwatch_rest_at(
                                    s, Mroute, values, levels_entry) *
                                  has_permission(&false_lit)
                             */
                        /*@ Given retained_route garbage_route */
                        /*@ solver_propagation_nonwatch_rest_at(
                              s, Mroute, values, levels_entry)
                            which implies exists rsn_route trl_route,
                              store(&(s->qhead), int,
                                mt_qhead(ms_core(Mroute))) *
                              store(&(s->qtail), int,
                                ms_qtail(Mroute)) *
                              store(&(s->simpdb_props), int,
                                ms_simpdb_props(Mroute)) *
                              store(&(s->assigns), lbool *, values) *
                              store(&(s->levels), int *, levels_entry) *
                              store(&(s->reasons), clause **,
                                rsn_route) *
                              store(&(s->trail), lit *, trl_route) *
                              CharArray::seg(
                                values, 0, ms_size(Mroute),
                                mt_assigns(ms_core(Mroute))) *
                              CharArray::undef_seg(
                                values, ms_size(Mroute),
                                ms_cap(Mroute)) *
                              IntArray::seg(
                                levels_entry, 0, ms_size(Mroute),
                                mt_levels(ms_core(Mroute))) *
                              IntArray::undef_seg(
                                levels_entry, ms_size(Mroute),
                                ms_cap(Mroute)) *
                              PtrArray::seg(
                                rsn_route, 0, ms_size(Mroute),
                                ms_reason_words(Mroute)) *
                              PtrArray::undef_seg(
                                rsn_route, ms_size(Mroute),
                                ms_cap(Mroute)) *
                              IntArray::seg(
                                trl_route, 0, ms_qtail(Mroute),
                                mt_trail(ms_core(Mroute))) *
                              IntArray::undef_seg(
                                trl_route, ms_qtail(Mroute),
                                ms_cap(Mroute)) *
                              veci_rep(
                                &(s->trail_lim),
                                mt_lim(ms_core(Mroute)),
                                ms_lim_cap(Mroute)) *
                              store(&(s->binary), clause *,
                                ms_binary(Mroute)) *
                              solver_binary_rep(Mroute) *
                              store(&(s->stats.propagations),
                                unsigned long long,
                                stats_propagations(ms_stats(Mroute))) *
                              store(&(s->stats.inspects),
                                unsigned long long,
                                stats_inspects(ms_stats(Mroute))) *
                              solver_propagate_frame(s, Mroute)
                         */
                        /*@ Branch name unit_conflict */
                        // BREAK BRIDGE.  This is a verbatim copy of the scan loop's bottom
                        // merge assertion, plus `i >= endvar`.  The `break` below leaves the
                        // loop from this arm rather than falling through to that merge, so the
                        // same entailment is paid here and the loop-exit merge absorbs all
                        // three exits in one shape.
                        /*@ Assert exists Mnext memory_next logical_next,
                                  exists next_wm_pre next_wm_post,
                                  exists next_caps_pre next_caps_post next_wcap,
                                  exists retained_next moved_next rest_next garbage_next,
                                  exists ii_next jj_next prop_count_next simp_count_next,
                                  exists rsn_next lvl_next trl_next,
                                  exists Mentry_next source_words_next,
                                  i >= endvar &&
                                  lvl_next == levels_entry &&
                                  s == s@pre && conflict_out == conflict_out@pre &&
                          values == assigns_entry && solver_shape(Mnext) &&
                                  msolver_seed_shadow(Mnext) &&
                                  propagation_caller_frame(M0, Mnext) &&
                                  propagation_scan_frontier( Mentry_next, Mnext, p) &&
                                  solver_propagation_scan_semantics(
                                    n, F, A_arr, K, Mnext, p, confl,
                                    retained_next, rest_next) &&
                                  minisat_propagation_reuse_scan(M0, Mnext, p, confl, rest_next) &&
                                  propagation_watch_scan_physical(
                                    source_words_next, retained_next, moved_next,
                                    rest_next, garbage_next, memory_next,
                                    ii_next, jj_next) &&
                                  logical_next == app(retained_next, rest_next) &&
                                  ms_wm(Mnext) ==
                                    app(next_wm_pre,
                                      cons(logical_next, next_wm_post)) &&
                                  ms_wcaps(Mnext) ==
                                    app(next_caps_pre,
                                      cons(next_wcap, next_caps_post)) &&
                                  Zlength(next_wm_pre) == p &&
                                  Zlength(next_caps_pre) == p &&
                                  ws == vecp_slot(wlists_entry, p) &&
                                  endvar == begin + Zlength(source_words_next) &&
                                  Zlength(memory_next) == Zlength(source_words_next) &&
                                  i == begin + ii_next &&
                                  j == begin + jj_next &&
                                  0 <= jj_next && jj_next <= ii_next &&
                                  0 <= ii_next &&
                                  ii_next <= Zlength(source_words_next) &&
                                  (ii_next != 0 ||
                                   Mnext == msolver_propagation_scan_begin(
                                     Mentry_next, simp_count_next, prop_count_next)) &&
                                  simp_count_next == ms_simpdb_props(Mnext) &&
                                  prop_count_next == stats_propagations(ms_stats(Mnext)) &&
                                  0 <= Zlength(source_words_next) &&
                                  Zlength(source_words_next) <= next_wcap &&
                                  0 < next_wcap && next_wcap <= INT_MAX &&
                                  store(&(ws->size), int, Zlength(source_words_next)) *
                                  store(&(ws->cap), int, next_wcap) *
                                  store(&(ws->ptr), void **, begin) *
                                  PtrArray::full(
                                    begin, Zlength(source_words_next), memory_next) *
                                  PtrArray::undef_seg(
                                    begin, Zlength(source_words_next), next_wcap) *
                                  wlists_source_hole_handle(
                                    s, wlists_entry, Zlength(next_wm_pre),
                                    next_wm_pre, next_wm_post,
                                    next_caps_pre, next_caps_post) *
                                  clause_db_rep(ms_prob(Mnext)) *
                                  clause_db_rep(ms_learnt(Mnext)) *
                                  store(&(s->reasons), clause **, rsn_next) *
                                  store(&(s->levels), int *, lvl_next) *
                                  store(&(s->trail), lit *, trl_next) *
                                  CharArray::seg(
                                    values, 0, ms_size(Mnext),
                                    mt_assigns(ms_core(Mnext))) *
                                  CharArray::undef_seg(
                                    values, ms_size(Mnext), ms_cap(Mnext)) *
                                  store(&(s->qhead), int,
                                    mt_qhead(ms_core(Mnext))) *
                                  solver_propagation_scan_core_at(
                                    s, Mnext, values, rsn_next, lvl_next, trl_next,
                                    simp_count_next, prop_count_next) *
                                  data_at(conflict_out, 0) *
                                  has_permission(&(lits)) *
                                  has_permission(&sig) *
                                  has_permission(&k) *
                                  has_permission(&stop) *
                                  has_permission(&false_lit)
                             */
                            break;
                        }
                    /*@ ii <= jj && jj <= ii &&
                                Zlength(candidate_post_memory) ==
                                  Zlength(source_words) &&
                                propagation_ptr_segment(
                                  begin, 0, ii,
                                  sublist(
                                    0, ii,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + ii * sizeof(struct clause_t *),
                                  struct clause_t *, scan_current) *
                                propagation_ptr_segment(
                                  begin, ii + 1,
                                  Zlength(source_words),
                                  sublist(ii + 1,
                                    Zlength(source_words),
                                    candidate_post_memory))
                                $ unit_same
                                which implies
                                PtrArray::full(
                                  begin, Zlength(source_words),
                                  replace_Znth(
                                    jj, scan_current,
                                    candidate_post_memory))
                                $ unit_same
                             */
                    /*@ Znth(ii, candidate_post_memory, 0) == scan_current &&
                                Zlength(candidate_post_memory) ==
                                  Zlength(source_words) &&
                                propagation_ptr_segment(
                                  begin, 0, jj,
                                  sublist(
                                    0, jj,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + jj * sizeof(struct clause_t *),
                                  struct clause_t *, scan_current) *
                                propagation_ptr_segment(
                                  begin, jj + 1, ii,
                                  sublist(jj + 1, ii,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + ii * sizeof(struct clause_t *),
                                  struct clause_t *, scan_current) *
                                propagation_ptr_segment(
                                  begin, ii + 1,
                                  Zlength(source_words),
                                  sublist(ii + 1,
                                    Zlength(source_words),
                                    candidate_post_memory))
                                $ unit_move
                                which implies
                                PtrArray::full(
                                  begin, Zlength(source_words),
                                  replace_Znth(
                                    jj, scan_current,
                                    candidate_post_memory))
                                $ unit_move
                             */
                    // No `exists` on this join, and no trailing `Given`: the conflict
                    // arm above FALLS THROUGH (no break/return), so three branches
                    // are live here -- `unit_conflict`, plus `unit_same`/`unit_move`
                    // still carried by the success path from the producer earlier in this function.
                    // A join names only the branches it merges, so `unit_conflict`
                    // survives it; an `exists` here would put a name in the merged
                    // success branch's exist list that `unit_conflict` does not have,
                    // and the `Given` would then fail on that branch.  The
                    // name was never used downstream, so the join simply states the
                    // merged assertion directly.
                    /*@ Branch join unit_same unit_move with
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    replace_Znth(
                                      jj, scan_current,
                                      candidate_post_memory))
                             */
                    /*@ Given Mentry source_words Mscan watch_memory candidate_post_memory
                              logical_words scan_wm_pre scan_wm_post scan_caps_pre
                              scan_caps_post scan_wcap retained moved rest garbage ii jj
                              prop_count simp_count scan_current raw_suffix clause_contents
                              watch0 */
                    /*@ exists unit_ret,
                                unit_ret != 0 &&
                                solver_propagation_scan_semantics(
                                  n, F, A_arr, K, Mscan, p, 0,
                                  retained, rest) &&
                                minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                                rest ==
                                  cons(scan_current, raw_suffix) &&
                                propagation_watch_scan_physical(
                                  source_words, retained, moved, rest,
                                  garbage, watch_memory, ii, jj) &&
                                candidate_post_memory == watch_memory &&
                                Znth(ii, candidate_post_memory, 0) ==
                                  scan_current &&
                                false_lit == lit_neg_c(p) &&
                                real_watch_pair(
                                  Zlength(scan_wm_pre), clause_contents) &&
                                watch0 + false_lit ==
                                  Znth(0, clause_contents, 0) +
                                  Znth(1, clause_contents, 0) &&
                                propagation_replacement_scan_inv(
                                  n, Mscan, false_lit,
                                  propagation_normalized_clause(
                                    watch0, false_lit, clause_contents),
                                  Zlength(clause_contents)) &&
                                clause_lits_pointer(
                                  scan_current, lits) &&
                                clause_db_pair_frame(
                                  ms_prob(Mscan), ms_learnt(Mscan),
                                  scan_current, clause_contents) *
                                store(
                                  lits + 0 * sizeof(int), int, watch0) *
                                store(
                                  lits + 1 * sizeof(int), int,
                                  false_lit) *
                                IntArray::seg(
                                  lits, 2,
                                  Zlength(clause_contents),
                                  sublist(2,
                                    Zlength(clause_contents),
                                    clause_contents)) *
                                enqueue_post_at(
                                  s, values, levels_entry,
                                  watch0,
                                  Znth(ii, candidate_post_memory, 0),
                                  ms_size(Mscan), ms_cap(Mscan),
                                  ms_qtail(Mscan), unit_ret,
                                  mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)),
                                  ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan)),
                                  mt_lim(ms_core(Mscan)),
                                  ms_lim_cap(Mscan))
                              $ unnamed
                              which implies
                              exists prob_route learnt_route Mroute,
                                exists retained_route rest_route,
                                exists garbage_route memory_route,
                                db_pair_lits_update(
                                  ms_prob(Mscan), ms_learnt(Mscan),
                                  scan_current, clause_contents,
                                  propagation_normalized_clause(
                                    watch0, false_lit,
                                    clause_contents),
                                  prob_route, learnt_route) &&
                                retained_route ==
                                  app(retained,
                                    cons(scan_current, nil)) &&
                                rest_route == raw_suffix &&
                                propagation_unit_success_transition(
                                  n, F, A_arr, K, Mscan, p,
                                  watch0, scan_current,
                                  propagation_normalized_clause(
                                    watch0, false_lit,
                                    clause_contents),
                                  prob_route, learnt_route,
                                  retained_route, rest_route,
                                  Mroute) &&
                                minisat_propagation_reuse_scan(M0, Mroute, p, 0, rest_route) &&
                                propagation_scan_keep_step(
                                  source_words, retained, moved, rest,
                                  watch_memory, ii, jj,
                                  scan_current, retained_route,
                                  rest_route, garbage_route,
                                  memory_route) &&
                                clause_db_rep(prob_route) *
                                clause_db_rep(learnt_route) *
                                enqueue_post_at(
                                  s, values, levels_entry,
                                  watch0, scan_current,
                                  ms_size(Mscan), ms_cap(Mscan),
                                  ms_qtail(Mscan), 1,
                                  mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)),
                                  ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan)),
                                  mt_lim(ms_core(Mscan)),
                                  ms_lim_cap(Mscan)) *
                                has_permission(&lits)
                             */
                    /*@ Given prob_route learnt_route Mroute */
                    // No `Given rest_route`.  The `which implies` above is `$ unnamed`, so
                    // it runs only on the merged success branch; the `Given`s below it run
                    // on EVERY live branch, and `unit_conflict` (the fall-through arm) has
                    // no `rest_route` in its exist list.  The four
                    // names above it do exist on both branches.  `rest_route` is never
                    // referenced after this point: the migrated route transition is now
                    // folded before `break`, so the `Given` was dead and is simply dropped.
                    /*@ Branch name unit_success */
                    }
                /* The replacement-success transition is completed at the
                   historical tagged boundary.  Its spatial LHS fixes the two
                   loop-local route witnesses without any post-loop Given. */
                /*@ Branch name real_migrated: offset != Zlength(clause_contents) */
                /*@ exists candidate destination_index destination_ptr destination_base destination_cap,
                    exists destination_words migration_post_memory,
                      solver_shape(Mscan) && msolver_seed_shadow(Mscan) && propagation_caller_frame(M0, Mscan) &&
                      propagation_scan_frontier(Mentry, Mscan, p) &&
                      solver_propagation_scan_semantics(n, F, A_arr, K, Mscan, p, 0, retained, rest) &&
                      minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                      rest == cons(scan_current, raw_suffix) &&
                      propagation_watch_scan_physical(source_words, retained, moved, rest,
                        garbage, watch_memory, ii, jj) &&
                      candidate_post_memory == watch_memory && 0 <= ii && ii < Zlength(source_words) &&
                      Znth(ii, candidate_post_memory, 0) == scan_current && migration_post_memory ==
                        replace_Znth(ii, Znth(ii, candidate_post_memory, 0), candidate_post_memory) &&
                      Znth(ii, migration_post_memory, 0) == scan_current &&
                      Zlength(scan_wm_pre) == p && false_lit == lit_neg_c(p) &&
                      real_watch_pair(Zlength(scan_wm_pre), clause_contents) &&
                      watch0 + false_lit == Znth(0, clause_contents, 0) +
                        Znth(1, clause_contents, 0) &&
                      propagation_replacement_scan_inv(n, Mscan, false_lit,
                        propagation_normalized_clause(watch0, false_lit, clause_contents), offset) &&
                      propagation_scan_candidate_layout(scan_current, lits, stop, k, offset,
                        false_lit, p, candidate, 2 * lit_sign_c(candidate) - 1, clause_contents) &&
                      Znth(lit_var_c(candidate), mt_assigns(ms_core(Mscan)), 0) !=
                        2 * lit_sign_c(candidate) - 1 &&
                      propagation_destination_index(2 * ms_size(Mscan), p, lit_neg_c(candidate)) &&
                      propagation_real_migrated_physical_alias(
                        wlists_entry, Zlength(scan_wm_pre), lit_neg_c(candidate), scan_current,
                        destination_index, destination_ptr, scan_wm_pre, scan_wm_post,
                        destination_words) &&
                      propagation_scan_slot(Mscan, p, scan_wm_pre, logical_words, scan_wm_post,
                        scan_caps_pre, scan_wcap, scan_caps_post) &&
                      simp_count == ms_simpdb_props(Mscan) &&
                      prop_count == stats_propagations(ms_stats(Mscan)) &&
                      0 <= Zlength(destination_words) &&
                      Zlength(destination_words) <= destination_cap &&
                      0 < destination_cap && destination_cap <= INT_MAX &&
                      clause_lits_pointer(scan_current, lits) &&
                      clause_db_pair_frame(ms_prob(Mscan), ms_learnt(Mscan),
                        scan_current, clause_contents) *
                      store(lits + 0 * sizeof(int), int, watch0) *
                      store(lits + 1 * sizeof(int), int, candidate) *
                      IntArray::seg(lits, 2, Zlength(clause_contents),
                        replace_Znth(offset - 2, false_lit,
                          replace_Znth(offset - 2, candidate,
                            sublist(2, Zlength(clause_contents), clause_contents)))) *
                      PtrArray::full(begin, Zlength(source_words), migration_post_memory) *
                      solver_wlists_handle(s, wlists_entry) *
                      wlists_split_except_two(wlists_entry, Zlength(scan_wm_pre), destination_index,
                        scan_wm_pre, scan_wm_post, scan_caps_pre, scan_caps_post) *
                      store(vecp_size_addr(destination_ptr), int,
                        Zlength(destination_words)) *
                      store(vecp_cap_addr(destination_ptr), int, destination_cap) *
                      store(vecp_ptr_addr(destination_ptr), void **, destination_base) *
                      PtrArray::full(destination_base, Zlength(destination_words),
                        destination_words) *
                      PtrArray::undef_seg(destination_base,
                        Zlength(destination_words), destination_cap)
                    $ real_migrated
                    which implies
                      exists prob_route learnt_route Mroute,
                        exists moved_route rest_route garbage_route,
                        db_pair_lits_update(ms_prob(Mscan), ms_learnt(Mscan),
                          scan_current, clause_contents,
                          propagation_migrated_clause(watch0, candidate, false_lit,
                            offset, clause_contents), prob_route, learnt_route) &&
                        moved_route == app(moved, cons(scan_current, nil)) &&
                        rest_route == raw_suffix &&
                        propagation_real_migrated_exit_carrier(n, F, A_arr, K,
                          M0, Mentry, Mscan, Mroute, p, prob_route, learnt_route,
                          scan_wm_pre, scan_wm_post, scan_caps_pre, scan_caps_post,
                          scan_wcap, destination_cap, candidate, scan_current,
                          source_words, retained, moved, rest, watch_memory, ii, jj,
                          moved_route, rest_route, garbage_route,
                          migration_post_memory, simp_count, prop_count) &&
                        minisat_propagation_reuse_scan(M0, Mroute, p, 0, rest_route) &&
                        clause_db_rep(prob_route) * clause_db_rep(learnt_route) *
                        wlists_source_hole_handle(s, wlists_entry, Zlength(scan_wm_pre),
                          propagation_split_pre_words(Zlength(scan_wm_pre),
                            destination_index, scan_wm_pre, destination_words),
                          propagation_split_post_words(Zlength(scan_wm_pre),
                            destination_index, scan_wm_post, destination_words),
                          propagation_split_pre_caps(Zlength(scan_wm_pre),
                            destination_index, scan_caps_pre, destination_cap),
                          propagation_split_post_caps(Zlength(scan_wm_pre),
                            destination_index, scan_caps_post, destination_cap)) *
                        PtrArray::full(begin, Zlength(source_words), migration_post_memory) *
                        has_permission(&k) * has_permission(&lits) *
                        has_permission(&stop)
                    $ real_migrated
                 */
                }
            }
            i++;
        // `prop_count_next` / `simp_count_next` are bound below for the same reason as
        // `ii_next` / `jj_next`: this loop's own Inv Assert binds `ii jj prop_count simp_count`
        // as ITS OWN existentials (named by the `Given`s that follow it), so this merge
        // assertion must re-bind all four, not two.  Referring to the given counters here
        // is the "Using given variable that does not belong to this branch" error.
        // Nothing is weakened: in
        // both assertions the counters are pinned by definitional equations to projections
        // of the state in scope, and they are mutated only once, before this loop begins.
        /*@ Assert exists Mnext memory_next logical_next,
                  exists next_wm_pre next_wm_post,
                  exists next_caps_pre next_caps_post next_wcap,
                  exists retained_next moved_next rest_next garbage_next,
                  exists ii_next jj_next prop_count_next simp_count_next,
                  exists rsn_next lvl_next trl_next,
                  exists Mentry_next source_words_next,
                  lvl_next == levels_entry &&
                  s == s@pre && conflict_out == conflict_out@pre &&
          values == assigns_entry && solver_shape(Mnext) &&
                  msolver_seed_shadow(Mnext) &&
                  propagation_caller_frame(M0, Mnext) &&
                  propagation_scan_frontier( Mentry_next, Mnext, p) &&
                  solver_propagation_scan_semantics(
                    n, F, A_arr, K, Mnext, p, confl,
                    retained_next, rest_next) &&
                  minisat_propagation_reuse_scan(M0, Mnext, p, confl, rest_next) &&
                  propagation_watch_scan_physical(
                    source_words_next, retained_next, moved_next,
                    rest_next, garbage_next, memory_next,
                    ii_next, jj_next) &&
                  logical_next == app(retained_next, rest_next) &&
                  ms_wm(Mnext) ==
                    app(next_wm_pre,
                      cons(logical_next, next_wm_post)) &&
                  ms_wcaps(Mnext) ==
                    app(next_caps_pre,
                      cons(next_wcap, next_caps_post)) &&
                  Zlength(next_wm_pre) == p &&
                  Zlength(next_caps_pre) == p &&
                  ws == vecp_slot(wlists_entry, p) &&
                  endvar == begin + Zlength(source_words_next) &&
                  Zlength(memory_next) == Zlength(source_words_next) &&
                  i == begin + ii_next &&
                  j == begin + jj_next &&
                  0 <= jj_next && jj_next <= ii_next &&
                  0 <= ii_next &&
                  ii_next <= Zlength(source_words_next) &&
                  (ii_next != 0 ||
                   Mnext == msolver_propagation_scan_begin(
                     Mentry_next, simp_count_next, prop_count_next)) &&
                  simp_count_next == ms_simpdb_props(Mnext) &&
                  prop_count_next == stats_propagations(ms_stats(Mnext)) &&
                  0 <= Zlength(source_words_next) &&
                  Zlength(source_words_next) <= next_wcap &&
                  0 < next_wcap && next_wcap <= INT_MAX &&
                  store(&(ws->size), int, Zlength(source_words_next)) *
                  store(&(ws->cap), int, next_wcap) *
                  store(&(ws->ptr), void **, begin) *
                  PtrArray::full(
                    begin, Zlength(source_words_next), memory_next) *
                  PtrArray::undef_seg(
                    begin, Zlength(source_words_next), next_wcap) *
                  wlists_source_hole_handle(
                    s, wlists_entry, Zlength(next_wm_pre),
                    next_wm_pre, next_wm_post,
                    next_caps_pre, next_caps_post) *
                  clause_db_rep(ms_prob(Mnext)) *
                  clause_db_rep(ms_learnt(Mnext)) *
                  store(&(s->reasons), clause **, rsn_next) *
                  store(&(s->levels), int *, lvl_next) *
                  store(&(s->trail), lit *, trl_next) *
                  CharArray::seg(
                    values, 0, ms_size(Mnext),
                    mt_assigns(ms_core(Mnext))) *
                  CharArray::undef_seg(
                    values, ms_size(Mnext), ms_cap(Mnext)) *
                  store(&(s->qhead), int,
                    mt_qhead(ms_core(Mnext))) *
                  solver_propagation_scan_core_at(
                    s, Mnext, values, rsn_next, lvl_next, trl_next,
                    simp_count_next, prop_count_next) *
                  data_at(conflict_out, 0) *
                  has_permission(&(lits))
             */
        }

        /* LOOP-EXIT MERGE.  Three exits reach
           here: the scan running out (`i >= endvar` from the negated condition,
           state = this loop's own `Inv Assert`) and the two conflict `break`s,
           which arrive carrying the bottom merge assertion.  This restates the
           invariant with `i >= endvar` so every exit leaves in ONE shape and the
           `Given` below binds the same 21 witnesses on all of them.  For the two
           break arms this is the same entailment the back edge pays at the loop
           head.
           It is a `Branch join`, not a plain `Assert`: an `Assert` groups by branch
           name and would leave three same-shaped branches alive, re-executing the
           whole post-loop tail (`vecp_begin` x2, `vecp_resize`, the `Mfinish` merge)
           once per branch.  The three exits genuinely converge here -- same records,
           same heap, the conflict distinction already carried by `confl` -- so they
           are joined explicitly into one. */
        /*@ Branch join binary_conflict unit_conflict unnamed with
            Assert exists Mscan watch_memory logical_words,
              exists scan_wm_pre scan_wm_post scan_caps_pre scan_caps_post,
              exists scan_wcap retained moved rest garbage,
              exists ii jj prop_count simp_count,
              exists rsn_scan trl_scan Mentry source_words,
              i >= endvar &&
              s == s@pre && conflict_out == conflict_out@pre &&
          values == assigns_entry &&
              solver_shape(Mscan) &&
              msolver_seed_shadow(Mscan) &&
              propagation_caller_frame(M0, Mscan) &&
              propagation_scan_frontier(Mentry, Mscan, p) &&
              solver_propagation_scan_semantics(
                n, F, A_arr, K, Mscan, p, confl, retained, rest) &&
              minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
              propagation_watch_scan_physical(
                source_words, retained, moved, rest, garbage,
                watch_memory, ii, jj) &&
              logical_words == app(retained, rest) &&
              ms_wm(Mscan) ==
                app(scan_wm_pre, cons(logical_words, scan_wm_post)) &&
              ms_wcaps(Mscan) ==
                app(scan_caps_pre, cons(scan_wcap, scan_caps_post)) &&
              Zlength(scan_wm_pre) == p &&
              Zlength(scan_caps_pre) == p &&
              ws == vecp_slot(wlists_entry, p) &&
              endvar == begin + Zlength(source_words) &&
              Zlength(watch_memory) == Zlength(source_words) &&
              i == begin + ii && j == begin + jj &&
              0 <= jj && jj <= ii &&
              0 <= ii && ii <= Zlength(source_words) &&
              (ii != 0 ||
               Mscan == msolver_propagation_scan_begin(
                      Mentry, simp_count, prop_count)) &&
              simp_count == ms_simpdb_props(Mscan) &&
              prop_count == stats_propagations(ms_stats(Mscan)) &&
              0 <= Zlength(source_words) &&
              Zlength(source_words) <= scan_wcap &&
              0 < scan_wcap && scan_wcap <= INT_MAX &&
              store(&(ws->size), int, Zlength(source_words)) *
              store(&(ws->cap), int, scan_wcap) *
              store(&(ws->ptr), void **, begin) *
              PtrArray::full(
                begin, Zlength(source_words), watch_memory) *
              PtrArray::undef_seg(
                begin, Zlength(source_words), scan_wcap) *
              wlists_source_hole_handle(
                s, wlists_entry, Zlength(scan_wm_pre),
                scan_wm_pre, scan_wm_post, scan_caps_pre, scan_caps_post) *
              clause_db_rep(ms_prob(Mscan)) *
              clause_db_rep(ms_learnt(Mscan)) *
              CharArray::seg(
                values, 0, ms_size(Mscan),
                mt_assigns(ms_core(Mscan))) *
              CharArray::undef_seg(
                values, ms_size(Mscan), ms_cap(Mscan)) *
              store(&(s->reasons), clause **, rsn_scan) *
              store(&(s->levels), int *, levels_entry) *
              store(&(s->trail), lit *, trl_scan) *
              PtrArray::seg(
                rsn_scan, 0, ms_size(Mscan),
                ms_reason_words(Mscan)) *
              PtrArray::undef_seg(
                rsn_scan, ms_size(Mscan), ms_cap(Mscan)) *
              IntArray::seg(
                levels_entry, 0, ms_size(Mscan),
                mt_levels(ms_core(Mscan))) *
              IntArray::undef_seg(
                levels_entry, ms_size(Mscan), ms_cap(Mscan)) *
              IntArray::seg(
                trl_scan, 0, ms_qtail(Mscan),
                mt_trail(ms_core(Mscan))) *
              IntArray::undef_seg(
                trl_scan, ms_qtail(Mscan), ms_cap(Mscan)) *
              veci_rep(
                &(s->trail_lim), mt_lim(ms_core(Mscan)),
                ms_lim_cap(Mscan)) *
              store(&(s->qhead), int,
                    mt_qhead(ms_core(Mscan))) *
              store(&(s->qtail), int, ms_qtail(Mscan)) *
              store(&(s->simpdb_props), int, simp_count) *
              store(&(s->assigns), lbool *, values) *
              store(&(s->binary), clause *, ms_binary(Mscan)) *
              solver_binary_rep(Mscan) *
              store(&(s->stats.propagations),
                    unsigned long long, prop_count) *
              store(&(s->stats.inspects), unsigned long long,
                    stats_inspects(ms_stats(Mscan))) *
              solver_propagate_frame(s, Mscan) *
              data_at(conflict_out, 0) *
              has_permission(&(lits))
        */

        /* Bind the scan-loop exit witnesses themselves.  In particular,
           Mscan is the record that roots the framed core/arrays in the loop
           invariant; re-existentialising it in the normalization cut below
           would permit an unrelated semantic record with the same watcher
           projection. */
        /*@ Given Mscan watch_memory logical_words
                  scan_wm_pre scan_wm_post
                  scan_caps_pre scan_caps_post scan_wcap
                  retained moved rest garbage
                  ii jj prop_count simp_count
                  rsn_scan trl_scan
                  Mentry source_words */

        // The RHS refolds
        // `vecp_rep(ws, watch_memory, scan_wcap)`, whose guard (defined in solver_qcp_lib.v, and re-emitted
        // as a right-side obligation by strategy rules 7/9) is
        // `0 <= Zlength l <= cap /\ 0 < cap <= INT_MAX`.  Nothing on this LHS bounded
        // `scan_wcap`: `PtrArray::undef_seg` degenerates to `emp` when hi < lo and
        // `solver_shape` bounds no INDIVIDUAL watcher capacity, so the wit was
        // `forall scan_wcap, ... |-- 0 < scan_wcap <= INT_MAX`.  The four conjuncts below
        // are byte-copied from the producing annotation, this scan loop's own `Inv Assert`
        // (they sit there immediately above the same five spatial atoms);
        // `Zlength(watch_memory) == Zlength(source_words)` then comes from the
        // `propagation_watch_scan_physical` already on this LHS.
        /*@ i >= endvar &&
              solver_shape(Mscan) &&
              msolver_seed_shadow(Mscan) &&
              propagation_caller_frame(M0, Mscan) &&
              propagation_scan_frontier(Mentry, Mscan, p) &&
              solver_propagation_scan_semantics(
                n, F, A_arr, K, Mscan, p, confl,
                retained, rest) &&
              minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
              propagation_watch_scan_physical(
                source_words, retained, moved,
                rest, garbage, watch_memory,
                ii, jj) &&
              logical_words == app(retained, rest) &&
              ms_wm(Mscan) ==
                app(scan_wm_pre,
                  cons(logical_words, scan_wm_post)) &&
              ms_wcaps(Mscan) ==
                app(scan_caps_pre,
                  cons(scan_wcap, scan_caps_post)) &&
              Zlength(scan_wm_pre) == p &&
              Zlength(scan_caps_pre) == p &&
              vecp_slot(wlists_entry, p) <= ws && ws <= vecp_slot(wlists_entry, p) &&
              endvar == begin + Zlength(source_words) &&
              i == begin + ii &&
              j == begin + jj &&
              0 <= Zlength(source_words) &&
              Zlength(source_words) <= scan_wcap &&
              0 < scan_wcap &&
              scan_wcap <= INT_MAX &&
              wlists_source_hole_handle(
                s, wlists_entry, Zlength(scan_wm_pre),
                scan_wm_pre, scan_wm_post,
                scan_caps_pre, scan_caps_post) *
              store(&(ws->size), int,
                    Zlength(source_words)) *
              store(&(ws->cap), int, scan_wcap) *
              store(&(ws->ptr), void **, begin) *
              PtrArray::full(
                begin, Zlength(source_words), watch_memory) *
              PtrArray::undef_seg(
                begin, Zlength(source_words), scan_wcap)
            which implies
              solver_shape(Mscan) &&
              msolver_seed_shadow(Mscan) &&
              propagation_caller_frame(M0, Mscan) &&
              propagation_scan_frontier(Mentry, Mscan, p) &&
              solver_propagation_scan_semantics(
                n, F, A_arr, K, Mscan, p, confl,
                retained, nil) &&
              minisat_propagation_reuse_scan(M0, Mscan, p, confl, nil) &&
              propagation_watch_scan_physical(
                source_words, retained, moved,
                nil, garbage, watch_memory,
                ii, jj) &&
              ii == Zlength(source_words) &&
              jj == Zlength(retained) &&
              ms_wm(Mscan) ==
                app(scan_wm_pre,
                  cons(retained, scan_wm_post)) &&
              ms_wcaps(Mscan) ==
                app(scan_caps_pre,
                  cons(scan_wcap, scan_caps_post)) &&
              Zlength(scan_wm_pre) == p &&
              Zlength(scan_caps_pre) == p &&
              ws == vecp_slot(wlists_entry, p) &&
              endvar == begin + Zlength(source_words) &&
              i == endvar &&
              j == begin + jj &&
              wlists_source_hole_handle(
                s, wlists_entry, Zlength(scan_wm_pre),
                scan_wm_pre, scan_wm_post,
                scan_caps_pre, scan_caps_post) *
              vecp_rep_at(ws, begin, watch_memory, scan_wcap)
         */
        // Keep the exposed vecp data base exact across both following
        // `vecp_begin` calls.  Their raw contracts preserve the same pointer field,
        // so `vecp_resize` receives `j - begin` and the final refold keeps the
        // intended retained prefix rather than a quotient from a fresh base.
        s->stats.inspects += j - (clause**)vecp_begin(ws);
        // `j == begin + jj` is copied from the producer so the pure size
        // equation uses the same exact base that the spatial carrier exposes.
        /*@ j == begin + jj
            which implies
            j - begin == jj
         */
        vecp_resize(ws,j - (clause**)vecp_begin(ws));
    /* The outer Inv Assert of this loop binds rsn and trl existentially, so those two
       are discharged by unification -- but it spells the levels cell as the
       With-ghost levels_entry, which no Assert can re-bind.  Only lvl_finish needs
       tying; see entail_wit_32_1/32_2.  This note sits OUTSIDE the annotation
       because BOTH C comment forms are syntax errors inside an annotation block. */
    /*@ Assert exists Mfinish rsn_finish lvl_finish trl_finish,
              lvl_finish == levels_entry &&
              s == s@pre && conflict_out == conflict_out@pre &&
          values == assigns_entry &&
              solver_shape(Mfinish) &&
              msolver_seed_shadow(Mfinish) &&
              ((confl == 0 &&
                propagation_scan_live_finalize(
                  n, F, A_arr, K, M0, Mscan, p,
                  jj, retained, Mfinish)) ||
               (confl != 0 &&
                propagation_scan_conflict_finalize(
                  n, F, A_arr, K, M0, Mscan, p, confl,
                  jj, retained, Mfinish))) &&
              solver_propagation_loop_inv(
                n, F, A_arr, K, M0, Mfinish, confl) &&
              minisat_propagation_reuse_loop(n, M0, Mfinish, confl) &&
              sublist(0, jj, watch_memory) ==
                retained &&
              ms_wm(Mfinish) ==
                app(scan_wm_pre,
                  cons(retained, scan_wm_post)) &&
              ms_wcaps(Mfinish) ==
                app(scan_caps_pre,
                  cons(scan_wcap, scan_caps_post)) &&
              0 <= mt_qhead(ms_core(Mfinish)) &&
              mt_qhead(ms_core(Mfinish)) <= ms_qtail(Mfinish) &&
              ms_qtail(Mfinish) <= ms_size(Mfinish) &&
              ms_size(Mfinish) <= ms_cap(Mfinish) &&
              Zlength(mt_trail(ms_core(Mfinish))) ==
                ms_qtail(Mfinish) &&
              store(&(s->qhead), int,
                    mt_qhead(ms_core(Mfinish))) *
              store(&(s->qtail), int, ms_qtail(Mfinish)) *
              store(&(s->simpdb_props), int,
                    ms_simpdb_props(Mfinish)) *
              store(&(s->wlists), vecp *, wlists_entry) *
              store(&(s->assigns), lbool *, values) *
              store(&(s->reasons), clause **, rsn_finish) *
              store(&(s->levels), int *, lvl_finish) *
              store(&(s->trail), lit *, trl_finish) *
              store(&(s->binary), clause *,
                    ms_binary(Mfinish)) *
              CharArray::seg(
                values, 0, ms_size(Mfinish),
                mt_assigns(ms_core(Mfinish))) *
              CharArray::undef_seg(
                values, ms_size(Mfinish), ms_cap(Mfinish)) *
              PtrArray::seg(
                rsn_finish, 0, ms_size(Mfinish),
                ms_reason_words(Mfinish)) *
              PtrArray::undef_seg(
                rsn_finish, ms_size(Mfinish), ms_cap(Mfinish)) *
              IntArray::seg(
                lvl_finish, 0, ms_size(Mfinish),
                mt_levels(ms_core(Mfinish))) *
              IntArray::undef_seg(
                lvl_finish, ms_size(Mfinish), ms_cap(Mfinish)) *
              IntArray::seg(
                trl_finish, 0, ms_qtail(Mfinish),
                mt_trail(ms_core(Mfinish))) *
              IntArray::undef_seg(
                trl_finish, ms_qtail(Mfinish), ms_cap(Mfinish)) *
              veci_rep(
                &(s->trail_lim), mt_lim(ms_core(Mfinish)),
                ms_lim_cap(Mfinish)) *
              wlists_rep(
                wlists_entry, ms_size(Mfinish),
                ms_wm(Mfinish), ms_wcaps(Mfinish)) *
              clause_db_rep(ms_prob(Mfinish)) *
              clause_db_rep(ms_learnt(Mfinish)) *
              solver_binary_rep(Mfinish) *
              store(&(s->stats.propagations),
                    unsigned long long,
                    stats_propagations(ms_stats(Mfinish))) *
              store(&(s->stats.inspects),
                    unsigned long long,
                    stats_inspects(ms_stats(Mfinish))) *
              solver_propagate_frame(s, Mfinish) *
              data_at(conflict_out, 0) *
              has_permission(&(lits)) *
              has_permission(&begin) * has_permission(&endvar) *
              has_permission(&i) * has_permission(&j) *
              has_permission(&ws)
         */
    }

    *conflict_out = confl;
    if (confl != 0)
        return 0;
    return 1;
}

/* Order two learnt clauses for the reduction sort: binary clauses come last,
   and among the rest the lower activity comes first.  Requires both pointers
   to be clauses of the learnt database, and leaves them unchanged. */
static inline int clause_cmp (const void* x, const void* y)
/*@ With (db : dbmap) (activities : list fp32)
    Require In(x, db_words(db)) && In(y, db_words(db)) &&
            learnt_sort_rep(db, activities)
    Ensure learnt_cmp_result(db, activities, x, y, __return) &&
           learnt_sort_rep(db, activities)
 */
{
    /*@ In(x, db_words(db)) && In(y, db_words(db)) &&
          learnt_sort_rep(db, activities)
        which implies
          ((x == y &&
            exists (x_words : list Z) (x_activity : fp32),
              0 < x && x % 2 == 0 &&
              msat_fp32_nonnegative(x_activity) &&
              store(clause_hdr_addr(x), int,
                    clause_hdr_word(msat_true, Zlength(x_words))) *
              store(clause_act_addr(x), float, x_activity) *
              IntArray::seg(clause_lits_addr(x), 0,
                            Zlength(x_words), x_words) *
              learnt_sort_alias_remainder(
                db, activities, x, x_words, x_activity)) ||
           (x != y &&
            exists (x_words y_words : list Z)
                   (x_activity y_activity : fp32),
              0 < x && x % 2 == 0 &&
              0 < y && y % 2 == 0 &&
              msat_fp32_nonnegative(x_activity) &&
              msat_fp32_nonnegative(y_activity) &&
              store(clause_hdr_addr(x), int,
                    clause_hdr_word(msat_true, Zlength(x_words))) *
              store(clause_act_addr(x), float, x_activity) *
              IntArray::seg(clause_lits_addr(x), 0,
                            Zlength(x_words), x_words) *
              store(clause_hdr_addr(y), int,
                    clause_hdr_word(msat_true, Zlength(y_words))) *
              store(clause_act_addr(y), float, y_activity) *
              IntArray::seg(clause_lits_addr(y), 0,
                            Zlength(y_words), y_words) *
              learnt_sort_two_remainder(
                db, activities,
                x, x_words, x_activity,
                y, y_words, y_activity)))
     */
    return clause_size((clause*)x) > 2 && (clause_size((clause*)y) == 2 || clause_activity((clause*)x) < clause_activity((clause*)y)) ? -1 : 1; }

/* Halve the learnt-clause database.  Sorts the learnt clauses worst first,
   then deletes those in the worse half, plus any in the better half whose
   activity is below the increment-derived limit, keeping every binary clause
   and every clause that is currently a reason.  The survivors are compacted. */
void solver_reducedb(solver* s)
/*@ With levels_ptr wl n (F : cnf) (A_arr A_inst : list literal)
         (M : msolver)
    Require solver_reducedb_pre_at(
              s, levels_ptr, n, F, A_arr, A_inst, M, wl)
    Ensure solver_reducedb_post_at(
             s, levels_ptr, n, F, A_arr, A_inst, M, wl)
 */
{
    /*@ solver_reducedb_pre_at(
          s, levels_ptr, n, F, A_arr, A_inst, M, wl)
        which implies exists reasons_ptr,
          msolver_inv(n, F, A_arr, A_inst, M) &&
          mt_qhead(ms_core(M)) == ms_qtail(M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          learnt_sort_domain(ms_learnt(M), db_words(ms_learnt(M))) &&
          NoDup(db_words(ms_learnt(M))) &&
          store(&(s->size), ms_size(M)) *
          store(&(s->cla_inc), ms_cla_inc(M)) *
          store(&(s->wlists), wl) *
          wlists_rep(wl, ms_size(M), ms_wm(M), ms_wcaps(M)) *
          store(&(s->reasons), reasons_ptr) *
          PtrArray::seg(reasons_ptr, 0, ms_size(M), ms_reason_words(M)) *
          PtrArray::undef_seg(reasons_ptr, ms_size(M), ms_cap(M)) *
          vecp_rep(&(s->learnts), db_words(ms_learnt(M)),
                   ms_learnt_cap(M)) *
          clause_db_rep(ms_learnt(M)) *
          stats_rep(&(s->stats), ms_stats(M)) *
          solver_db_mutation_frame_at(s, M, levels_ptr)
     */
    /*@ Given reasons_ptr */
    int      i, j;
    float extra_lim = s->cla_inc / vecp_size(&s->learnts); // Remove any clause below this activity
    clause** learnts = (clause**)vecp_begin(&s->learnts);
    clause** reasons = s->reasons;

    sort(vecp_begin(&s->learnts), vecp_size(&s->learnts))
      /*@ where @mark reducedb_sort */;
    /*@ Given words_sorted from current of reducedb_sort */

    /*@ msolver_inv(n, F, A_arr, A_inst, M) &&
          mt_qhead(ms_core(M)) == ms_qtail(M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          learnt_sort_domain(ms_learnt(M), db_words(ms_learnt(M))) &&
          NoDup(db_words(ms_learnt(M))) &&
          Permutation(db_words(ms_learnt(M)), words_sorted) &&
          msat_fp32_count_limit(
            Zlength(db_words(ms_learnt(M))), extra_lim) &&
          0 < ms_learnt_cap(M) && ms_learnt_cap(M) <= INT_MAX &&
          Zlength(db_words(ms_learnt(M))) <= ms_learnt_cap(M) &&
          store(&(s->learnts.size), int,
                Zlength(db_words(ms_learnt(M)))) *
          store(&(s->learnts.cap), int, ms_learnt_cap(M)) *
          store(&(s->learnts.ptr), void **, learnts) *
          PtrArray::seg(learnts, 0, Zlength(db_words(ms_learnt(M))),
                        words_sorted) *
          PtrArray::undef_seg(learnts, Zlength(db_words(ms_learnt(M))),
                              ms_learnt_cap(M)) *
          clause_db_rep(ms_learnt(M))
        which implies exists (db_sorted : dbmap) (Msorted : msolver),
          Permutation(db_words(ms_learnt(M)), db_words(db_sorted)) &&
          db_words(db_sorted) == words_sorted &&
          Msorted == msolver_reorder_learnts(M, db_sorted) &&
          ms_model(Msorted) == ms_model(M) &&
          ms_cap(Msorted) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Msorted)) &&
          msat_fp32_same(ms_cla_decay(Msorted), ms_cla_decay(M)) &&
          msolver_inv(n, F, A_arr, A_inst, Msorted) &&
          mt_qhead(ms_core(Msorted)) == ms_qtail(Msorted) &&
          ms_capacity_root_propagation_pending(Msorted) == 0 &&
          msolver_seed_shadow(Msorted) &&
          db_compaction_inv(Msorted, words_sorted, 0, 0) &&
          msat_fp32_count_limit(Zlength(words_sorted), extra_lim) &&
          vecp_rep_at(&(s->learnts), learnts, words_sorted,
                      ms_learnt_cap(Msorted)) *
          clause_db_rep(ms_learnt(Msorted))
     */

    j = 0;
    /*@ Inv Assert exists (Mcur : msolver) (words : list Z),
          s == s@pre &&
          msolver_inv(n, F, A_arr, A_inst, Mcur) &&
          mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
          ms_capacity_root_propagation_pending(Mcur) == 0 &&
          msolver_seed_shadow(Mcur) &&
          ms_model(Mcur) == ms_model(M) &&
          ms_cap(Mcur) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Mcur)) &&
          msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
          reasons == reasons_ptr &&
          db_compaction_inv(Mcur, words, i, j) &&
          msat_fp32_count_limit(Zlength(words), extra_lim) &&
          0 <= j && j <= i && i <= Zlength(words) &&
          store(&(s->size), ms_size(Mcur)) *
          store(&(s->cla_inc), ms_cla_inc(Mcur)) *
          store(&(s->wlists), wl) *
          wlists_rep(wl, ms_size(Mcur), ms_wm(Mcur), ms_wcaps(Mcur)) *
          store(&(s->reasons), reasons_ptr) *
          PtrArray::seg(reasons_ptr, 0, ms_size(Mcur),
                        ms_reason_words(Mcur)) *
          PtrArray::undef_seg(reasons_ptr, ms_size(Mcur), ms_cap(Mcur)) *
          vecp_rep_at(&(s->learnts), learnts, words,
                      ms_learnt_cap(Mcur)) *
          clause_db_rep(ms_learnt(Mcur)) *
          stats_rep(&(s->stats), ms_stats(Mcur)) *
          solver_db_mutation_frame_at(s, Mcur, levels_ptr)
     */
    for (i = 0; i < vecp_size(&s->learnts) / 2; i++){
        /*@ Given Mcur words */
        /*@ db_compaction_inv(Mcur, words, i, j) &&
            msat_fp32_count_limit(Zlength(words), extra_lim) &&
            msolver_inv(n, F, A_arr, A_inst, Mcur) &&
            msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
            0 <= i && i < Zlength(words) &&
            clause_db_rep(ms_learnt(Mcur))
            which implies exists (lits_now : list Z)
                                 (activity_now : fp32),
              db_compaction_inv(Mcur, words, i, j) &&
              msat_fp32_count_limit(Zlength(words), extra_lim) &&
              msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
              msat_fp32_nonnegative(activity_now) &&
              0 <= i && i < Zlength(words) &&
              Forall(lit_wf_c(n), lits_now) &&
              clause_hdr_word(msat_true, Zlength(lits_now)) / 2 ==
                Zlength(lits_now) &&
              2 <= Zlength(lits_now) &&
              0 <= lit_var_c(lits_now[0 - 0]) &&
              lit_var_c(lits_now[0 - 0]) < ms_size(Mcur) &&
              0 < words[i - 0] && words[i - 0] % 2 == 0 &&
              store(clause_hdr_addr(words[i - 0]), int,
                    clause_hdr_word(msat_true, Zlength(lits_now))) *
              store(clause_act_addr(words[i - 0]), float, activity_now) *
              IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                            Zlength(lits_now), lits_now) *
              clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                       words[i - 0], msat_true, lits_now)
         */
        /*@ Given lits_now activity_now */
        if (clause_size(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i]))] != learnts[i]) {
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp32_count_limit(Zlength(words), extra_lim) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                msat_fp32_nonnegative(activity_now) &&
                0 <= j && j <= i && i < Zlength(words) &&
                2 <= Zlength(lits_now) &&
                0 < words[i - 0] && words[i - 0] % 2 == 0 &&
                ms_reason_words(Mcur)[lit_var_c(lits_now[0 - 0]) - 0] !=
                  words[i - 0] &&
                store(&(s->size), int, ms_size(Mcur)) *
                store(&(s->reasons), clause **, reasons_ptr) *
                PtrArray::seg(reasons_ptr, 0, ms_size(Mcur),
                              ms_reason_words(Mcur)) *
                PtrArray::undef_seg(reasons_ptr, ms_size(Mcur), ms_cap(Mcur)) *
                store(&(s->wlists), wl) *
                wlists_rep(wl, ms_size(Mcur), ms_wm(Mcur), ms_wcaps(Mcur)) *
                store(clause_hdr_addr(words[i - 0]), int,
                      clause_hdr_word(msat_true, Zlength(lits_now))) *
                store(clause_act_addr(words[i - 0]), float, activity_now) *
                IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                              Zlength(lits_now), lits_now) *
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                stats_rep(&(s->stats), ms_stats(Mcur))
                which implies
                  db_compaction_inv(Mcur, words, i, j) &&
                  msat_fp32_count_limit(Zlength(words), extra_lim) &&
                  msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                  0 <= j && j <= i &&
                  clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                           words[i - 0], msat_true,
                                           lits_now) *
                  clause_remove_pre(
                    s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), wl,
                    reasons_ptr, ms_wm(Mcur), ms_wcaps(Mcur), msat_true,
                    lits_now, ms_stats(Mcur), ms_reason_words(Mcur))
             */
            clause_remove(s,learnts[i]);
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp32_count_limit(Zlength(words), extra_lim) &&
                0 <= j && j <= i && i < Zlength(words) &&
                mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
                ms_capacity_root_propagation_pending(Mcur) == 0 &&
                msolver_seed_shadow(Mcur) &&
                ms_model(Mcur) == ms_model(M) &&
                  ms_cap(Mcur) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Mcur)) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                2 <= Zlength(lits_now) &&
                0 < words[i - 0] && words[i - 0] % 2 == 0 &&
                clause_remove_post(
                  s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), wl,
                  reasons_ptr, ms_wm(Mcur), ms_wcaps(Mcur), lits_now,
                  ms_stats(Mcur), ms_reason_words(Mcur)) *
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                store(&(s->cla_inc), ms_cla_inc(Mcur)) *
                vecp_rep_at(&(s->learnts), learnts, words,
                            ms_learnt_cap(Mcur)) *
                solver_db_mutation_frame_at(s, Mcur, levels_ptr)
                which implies exists (Mnext : msolver),
                  db_compaction_step(Mcur, words[i - 0], Mnext) &&
                  msolver_inv(n, F, A_arr, A_inst, Mnext) &&
                  mt_qhead(ms_core(Mnext)) == ms_qtail(Mnext) &&
                  ms_capacity_root_propagation_pending(Mnext) == 0 &&
                  msolver_seed_shadow(Mnext) &&
                  ms_model(Mnext) == ms_model(M) &&
                  ms_cap(Mnext) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Mnext)) &&
                  msat_fp32_same(ms_cla_decay(Mnext), ms_cla_decay(M)) &&
                  db_compaction_inv(Mnext, words, i + 1, j) &&
                  msat_fp32_count_limit(Zlength(words), extra_lim) &&
                  store(&(s->size), ms_size(Mnext)) *
                  store(&(s->cla_inc), ms_cla_inc(Mnext)) *
                  store(&(s->wlists), wl) *
                  wlists_rep(wl, ms_size(Mnext), ms_wm(Mnext),
                             ms_wcaps(Mnext)) *
                  store(&(s->reasons), reasons_ptr) *
                  PtrArray::seg(reasons_ptr, 0, ms_size(Mnext),
                                ms_reason_words(Mnext)) *
                  PtrArray::undef_seg(reasons_ptr, ms_size(Mnext),
                                      ms_cap(Mnext)) *
                  vecp_rep_at(&(s->learnts), learnts, words,
                              ms_learnt_cap(Mnext)) *
                  clause_db_rep(ms_learnt(Mnext)) *
                  stats_rep(&(s->stats), ms_stats(Mnext)) *
                  solver_db_mutation_frame_at(s, Mnext, levels_ptr)
             */
        }
        else {
            learnts[j] = learnts[i];
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp32_count_limit(Zlength(words), extra_lim) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                msat_fp32_nonnegative(activity_now) &&
                0 <= j && j <= i && i < Zlength(words) &&
                store(&(s->learnts.size), int, Zlength(words)) *
                store(&(s->learnts.cap), int, ms_learnt_cap(Mcur)) *
                store(&(s->learnts.ptr), void **, learnts) *
                PtrArray::full(learnts, Zlength(words),
                               replace_Znth(j, words[i - 0], words)) *
                PtrArray::undef_seg(learnts, Zlength(words),
                                    ms_learnt_cap(Mcur)) *
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                store(clause_hdr_addr(words[i - 0]), int,
                      clause_hdr_word(msat_true, Zlength(lits_now))) *
                store(clause_act_addr(words[i - 0]), float, activity_now) *
                IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                              Zlength(lits_now), lits_now)
                which implies
                  msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                  db_compaction_inv(Mcur,
                    replace_Znth(j, words[i - 0], words), i + 1, j + 1) &&
                  msat_fp32_count_limit(
                    Zlength(replace_Znth(j, words[i - 0], words)),
                    extra_lim) &&
                  0 <= j && j <= i && i < Zlength(words) &&
                  vecp_rep_at(&(s->learnts), learnts,
                              replace_Znth(j, words[i - 0], words),
                              ms_learnt_cap(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur))
             */
            j++;
        }
        /*@ Assert exists (Mnext : msolver) (words_next : list Z),
              s == s@pre &&
              db_compaction_step(Mcur, words[i - 0], Mnext) &&
              msolver_inv(n, F, A_arr, A_inst, Mnext) &&
              mt_qhead(ms_core(Mnext)) == ms_qtail(Mnext) &&
              ms_capacity_root_propagation_pending(Mnext) == 0 &&
              msolver_seed_shadow(Mnext) &&
              ms_model(Mnext) == ms_model(M) &&
          ms_cap(Mnext) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Mnext)) &&
              msat_fp32_same(ms_cla_decay(Mnext), ms_cla_decay(M)) &&
              reasons == reasons_ptr &&
              db_compaction_inv(Mnext, words_next, i + 1, j) &&
              msat_fp32_count_limit(Zlength(words_next), extra_lim) &&
              store(&(s->size), ms_size(Mnext)) *
              store(&(s->cla_inc), ms_cla_inc(Mnext)) *
              store(&(s->wlists), wl) *
              wlists_rep(wl, ms_size(Mnext), ms_wm(Mnext), ms_wcaps(Mnext)) *
              store(&(s->reasons), reasons_ptr) *
              PtrArray::seg(reasons_ptr, 0, ms_size(Mnext),
                            ms_reason_words(Mnext)) *
              PtrArray::undef_seg(reasons_ptr, ms_size(Mnext),
                                  ms_cap(Mnext)) *
              vecp_rep_at(&(s->learnts), learnts, words_next,
                          ms_learnt_cap(Mnext)) *
              clause_db_rep(ms_learnt(Mnext)) *
              stats_rep(&(s->stats), ms_stats(Mnext)) *
              solver_db_mutation_frame_at(s, Mnext, levels_ptr)
         */
    }
    /*@ Inv Assert exists (Mcur : msolver) (words : list Z),
          s == s@pre &&
          msolver_inv(n, F, A_arr, A_inst, Mcur) &&
          mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
          ms_capacity_root_propagation_pending(Mcur) == 0 &&
          msolver_seed_shadow(Mcur) &&
          ms_model(Mcur) == ms_model(M) &&
          ms_cap(Mcur) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Mcur)) &&
          msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
          reasons == reasons_ptr &&
          db_compaction_inv(Mcur, words, i, j) &&
          msat_fp32_count_limit(Zlength(words), extra_lim) &&
          0 <= j && j <= i && i <= Zlength(words) &&
          store(&(s->size), ms_size(Mcur)) *
          store(&(s->cla_inc), ms_cla_inc(Mcur)) *
          store(&(s->wlists), wl) *
          wlists_rep(wl, ms_size(Mcur), ms_wm(Mcur), ms_wcaps(Mcur)) *
          store(&(s->reasons), reasons_ptr) *
          PtrArray::seg(reasons_ptr, 0, ms_size(Mcur),
                        ms_reason_words(Mcur)) *
          PtrArray::undef_seg(reasons_ptr, ms_size(Mcur), ms_cap(Mcur)) *
          vecp_rep_at(&(s->learnts), learnts, words,
                      ms_learnt_cap(Mcur)) *
          clause_db_rep(ms_learnt(Mcur)) *
          stats_rep(&(s->stats), ms_stats(Mcur)) *
          solver_db_mutation_frame_at(s, Mcur, levels_ptr)
     */
    for (; i < vecp_size(&s->learnts); i++){
        /*@ Given Mcur words */
        /*@ db_compaction_inv(Mcur, words, i, j) &&
            msat_fp32_count_limit(Zlength(words), extra_lim) &&
            msolver_inv(n, F, A_arr, A_inst, Mcur) &&
            msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
            0 <= i && i < Zlength(words) &&
            clause_db_rep(ms_learnt(Mcur))
            which implies exists (lits_now : list Z)
                                 (activity_now : fp32),
              db_compaction_inv(Mcur, words, i, j) &&
              msat_fp32_count_limit(Zlength(words), extra_lim) &&
              msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
              msat_fp32_nonnegative(extra_lim) &&
              msat_fp32_nonnegative(activity_now) &&
              0 <= i && i < Zlength(words) &&
              Forall(lit_wf_c(n), lits_now) &&
              clause_hdr_word(msat_true, Zlength(lits_now)) / 2 ==
                Zlength(lits_now) &&
              2 <= Zlength(lits_now) &&
              0 <= lit_var_c(lits_now[0 - 0]) &&
              lit_var_c(lits_now[0 - 0]) < ms_size(Mcur) &&
              0 < words[i - 0] && words[i - 0] % 2 == 0 &&
              store(clause_hdr_addr(words[i - 0]), int,
                    clause_hdr_word(msat_true, Zlength(lits_now))) *
              store(clause_act_addr(words[i - 0]), float, activity_now) *
              IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                            Zlength(lits_now), lits_now) *
              clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                       words[i - 0], msat_true, lits_now)
         */
        /*@ Given lits_now activity_now */
        if (clause_size(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i]))] != learnts[i] && clause_activity(learnts[i]) < extra_lim) {
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp32_count_limit(Zlength(words), extra_lim) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                msat_fp32_nonnegative(extra_lim) &&
                msat_fp32_nonnegative(activity_now) &&
                0 <= j && j <= i && i < Zlength(words) &&
                2 <= Zlength(lits_now) &&
                0 < words[i - 0] && words[i - 0] % 2 == 0 &&
                ms_reason_words(Mcur)[lit_var_c(lits_now[0 - 0]) - 0] !=
                  words[i - 0] &&
                store(&(s->size), int, ms_size(Mcur)) *
                store(&(s->reasons), clause **, reasons_ptr) *
                PtrArray::seg(reasons_ptr, 0, ms_size(Mcur),
                              ms_reason_words(Mcur)) *
                PtrArray::undef_seg(reasons_ptr, ms_size(Mcur), ms_cap(Mcur)) *
                store(&(s->wlists), wl) *
                wlists_rep(wl, ms_size(Mcur), ms_wm(Mcur), ms_wcaps(Mcur)) *
                store(clause_hdr_addr(words[i - 0]), int,
                      clause_hdr_word(msat_true, Zlength(lits_now))) *
                store(clause_act_addr(words[i - 0]), float, activity_now) *
                IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                              Zlength(lits_now), lits_now) *
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                stats_rep(&(s->stats), ms_stats(Mcur))
                which implies
                  db_compaction_inv(Mcur, words, i, j) &&
                  msat_fp32_count_limit(Zlength(words), extra_lim) &&
                  msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                  0 <= j && j <= i &&
                  clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                           words[i - 0], msat_true,
                                           lits_now) *
                  clause_remove_pre(
                    s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), wl,
                    reasons_ptr, ms_wm(Mcur), ms_wcaps(Mcur), msat_true,
                    lits_now, ms_stats(Mcur), ms_reason_words(Mcur))
             */
            clause_remove(s,learnts[i]);
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp32_count_limit(Zlength(words), extra_lim) &&
                0 <= j && j <= i && i < Zlength(words) &&
                mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
                ms_capacity_root_propagation_pending(Mcur) == 0 &&
                msolver_seed_shadow(Mcur) &&
                ms_model(Mcur) == ms_model(M) &&
                  ms_cap(Mcur) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Mcur)) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                2 <= Zlength(lits_now) &&
                0 < words[i - 0] && words[i - 0] % 2 == 0 &&
                clause_remove_post(
                  s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), wl,
                  reasons_ptr, ms_wm(Mcur), ms_wcaps(Mcur), lits_now,
                  ms_stats(Mcur), ms_reason_words(Mcur)) *
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                store(&(s->cla_inc), ms_cla_inc(Mcur)) *
                vecp_rep_at(&(s->learnts), learnts, words,
                            ms_learnt_cap(Mcur)) *
                solver_db_mutation_frame_at(s, Mcur, levels_ptr)
                which implies exists (Mnext : msolver),
                  db_compaction_step(Mcur, words[i - 0], Mnext) &&
                  msolver_inv(n, F, A_arr, A_inst, Mnext) &&
                  mt_qhead(ms_core(Mnext)) == ms_qtail(Mnext) &&
                  ms_capacity_root_propagation_pending(Mnext) == 0 &&
                  msolver_seed_shadow(Mnext) &&
                  ms_model(Mnext) == ms_model(M) &&
                  ms_cap(Mnext) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Mnext)) &&
                  msat_fp32_same(ms_cla_decay(Mnext), ms_cla_decay(M)) &&
                  db_compaction_inv(Mnext, words, i + 1, j) &&
                  msat_fp32_count_limit(Zlength(words), extra_lim) &&
                  store(&(s->size), ms_size(Mnext)) *
                  store(&(s->cla_inc), ms_cla_inc(Mnext)) *
                  store(&(s->wlists), wl) *
                  wlists_rep(wl, ms_size(Mnext), ms_wm(Mnext),
                             ms_wcaps(Mnext)) *
                  store(&(s->reasons), reasons_ptr) *
                  PtrArray::seg(reasons_ptr, 0, ms_size(Mnext),
                                ms_reason_words(Mnext)) *
                  PtrArray::undef_seg(reasons_ptr, ms_size(Mnext),
                                      ms_cap(Mnext)) *
                  vecp_rep_at(&(s->learnts), learnts, words,
                              ms_learnt_cap(Mnext)) *
                  clause_db_rep(ms_learnt(Mnext)) *
                  stats_rep(&(s->stats), ms_stats(Mnext)) *
                  solver_db_mutation_frame_at(s, Mnext, levels_ptr)
             */
        }
        else {
            learnts[j] = learnts[i];
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp32_count_limit(Zlength(words), extra_lim) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                msat_fp32_nonnegative(activity_now) &&
                0 <= j && j <= i && i < Zlength(words) &&
                store(&(s->learnts.size), int, Zlength(words)) *
                store(&(s->learnts.cap), int, ms_learnt_cap(Mcur)) *
                store(&(s->learnts.ptr), void **, learnts) *
                PtrArray::full(learnts, Zlength(words),
                               replace_Znth(j, words[i - 0], words)) *
                PtrArray::undef_seg(learnts, Zlength(words),
                                    ms_learnt_cap(Mcur)) *
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                store(clause_hdr_addr(words[i - 0]), int,
                      clause_hdr_word(msat_true, Zlength(lits_now))) *
                store(clause_act_addr(words[i - 0]), float, activity_now) *
                IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                              Zlength(lits_now), lits_now)
                which implies
                  msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                  db_compaction_inv(Mcur,
                    replace_Znth(j, words[i - 0], words), i + 1, j + 1) &&
                  msat_fp32_count_limit(
                    Zlength(replace_Znth(j, words[i - 0], words)),
                    extra_lim) &&
                  0 <= j && j <= i && i < Zlength(words) &&
                  vecp_rep_at(&(s->learnts), learnts,
                              replace_Znth(j, words[i - 0], words),
                              ms_learnt_cap(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur))
             */
            j++;
        }
        /*@ Assert exists (Mnext : msolver) (words_next : list Z),
              s == s@pre &&
              db_compaction_step(Mcur, words[i - 0], Mnext) &&
              msolver_inv(n, F, A_arr, A_inst, Mnext) &&
              mt_qhead(ms_core(Mnext)) == ms_qtail(Mnext) &&
              ms_capacity_root_propagation_pending(Mnext) == 0 &&
              msolver_seed_shadow(Mnext) &&
              ms_model(Mnext) == ms_model(M) &&
          ms_cap(Mnext) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_base_watch_completed(Mnext)) &&
              msat_fp32_same(ms_cla_decay(Mnext), ms_cla_decay(M)) &&
              reasons == reasons_ptr &&
              db_compaction_inv(Mnext, words_next, i + 1, j) &&
              msat_fp32_count_limit(Zlength(words_next), extra_lim) &&
              store(&(s->size), ms_size(Mnext)) *
              store(&(s->cla_inc), ms_cla_inc(Mnext)) *
              store(&(s->wlists), wl) *
              wlists_rep(wl, ms_size(Mnext), ms_wm(Mnext), ms_wcaps(Mnext)) *
              store(&(s->reasons), reasons_ptr) *
              PtrArray::seg(reasons_ptr, 0, ms_size(Mnext),
                            ms_reason_words(Mnext)) *
              PtrArray::undef_seg(reasons_ptr, ms_size(Mnext),
                                  ms_cap(Mnext)) *
              vecp_rep_at(&(s->learnts), learnts, words_next,
                          ms_learnt_cap(Mnext)) *
              clause_db_rep(ms_learnt(Mnext)) *
              stats_rep(&(s->stats), ms_stats(Mnext)) *
              solver_db_mutation_frame_at(s, Mnext, levels_ptr)
         */
    }

    //printf("reducedb deleted %d\n", vecp_size(&s->learnts) - j);


    vecp_resize(&s->learnts,j);
}

/* One search restart: propagate, and on a conflict learn a clause, backjump
   and record it; otherwise simplify at the root, reduce the learnt database
   once it grows past `nof_learnts`, and take the next decision.  Returns 1
   with a model, 0 when the budget `nof_conflicts` runs out, -1 when the
   formula is refuted at the root level, or -2 out of capacity. */
static int solver_search(solver* s, int nof_conflicts, int nof_learnts)
/*@ With (search_wl : Z) (n : Z) (F : cnf) (A_arr A_inst : list literal) (M : msolver)
    Require solver_search_pre(s, n, F, A_arr, A_inst, M, search_wl)
    Ensure solver_search_result(s, n, F, A_arr, A_inst, __return, search_wl, M)
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
          IntArray::undef_seg(levels_entry, ms_size(M), ms_cap(M)) *
          solver_cancel_owned(s, M, search_wl)
     */
    /*@ Given levels_entry */
    int*    levels          = s->levels;
    double random_var_freq = 0.0199999995529651641845703125;

    uint64  conflictC       = 0;
    veci    learnt_clause;

    /*@ levels == levels_entry &&
          solver_shape(M) &&
          store(&(s->levels), int *, levels_entry) *
          IntArray::seg(levels_entry, 0, ms_size(M),
                        mt_levels(ms_core(M))) *
          IntArray::undef_seg(levels_entry, ms_size(M), ms_cap(M)) *
          solver_cancel_owned(s, M, search_wl)
        which implies solver_rep_levels_wl_at(s, M, search_wl, levels)
     */
    /*@ solver_rep_levels_wl_at(s, M, search_wl, levels)
        which implies
          store(&(s->root_level), int, ms_root_level(M)) *
          veci_rep(&(s->trail_lim),
                   mt_lim(ms_core(M)), ms_lim_cap(M)) *
          solver_search_root_frame_at(s, M, levels, search_wl)
     */
    /*@ solver_at_root(M)
        which implies
          ms_root_level(M) == Zlength(mt_lim(ms_core(M)))
     */
    assert(s->root_level == solver_dlevel(s));

    /*@ store(&(s->root_level), int, ms_root_level(M)) *
          veci_rep(&(s->trail_lim),
                   mt_lim(ms_core(M)), ms_lim_cap(M)) *
          solver_search_root_frame_at(s, M, levels, search_wl)
        which implies
          store(&(s->stats.starts), uint64, stats_starts(ms_stats(M))) *
          store(&(s->var_decay), double, ms_var_decay(M)) *
          store(&(s->cla_decay), float, ms_cla_decay(M)) *
          veci_rep(&(s->model), ms_model(M), ms_model_cap(M)) *
          solver_search_init_frame_at(s, M, levels, search_wl)
     */
    s->stats.starts++;
    s->var_decay = 1.0526316165924072265625;
    s->cla_decay = 1.00100100040435791015625f;
    veci_resize(&s->model,0);
    veci_new(&learnt_clause);

    /* This step is a `which implies' rather than a bare `exists (Minit :
       msolver), ..' assertion.  A bare assertion has to be DERIVED from the
       state, and no rule refolds `solver_search_init_frame_at' plus the four
       freshly written cells back into `solver_rep_levels_at' at a NEW msolver:
       the entry transition (starts++, the two decay constants, model := [])
       has no msolver constructor in the library.  As a `which implies' the RHS
       is ASSUMED and the obligation moves to Coq, where the record literal for
       `Minit' can simply be written out.  It folds straight to
       `solver_search_loop', so no second, equally underivable, bare step is
       needed. */
    /*@ exists starts_now (vd : fp64) (cd : fp32) learnt_ptr,
          msolver_inv(n, F, A_arr, A_inst, M) &&
          solver_at_root(M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          msat_fp32_positive_finite(cd) &&
          store(&(s->stats.starts), uint64, starts_now) *
          store(&(s->var_decay), double, vd) *
          store(&(s->cla_decay), float, cd) *
          veci_rep(&(s->model), sublist(0, 0, ms_model(M)),
                   ms_model_cap(M)) *
          solver_search_init_frame_at(s, M, levels, search_wl) *
          store(&(learnt_clause.size), int, 0) *
          store(&(learnt_clause.cap), int, 4) *
          store(&(learnt_clause.ptr), int *, learnt_ptr) *
          IntArray::seg(learnt_ptr, 0, 0, nil) *
          IntArray::undef_seg(learnt_ptr, 0, 4)
        which implies
          solver_search_loop(
            s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M)
     */
    /* `0 <= conflict_count_value' carries the uint64 range of `conflictC'
       into the loop body.  `minisat_conflict_limit_reached' has
       `Require 0 <= count && emp', and because the Require is `emp' the
       `conflictC' cell is FRAMED OUT of the call's obligation, so the range
       is unavailable there unless the invariant states it as a pure fact. */
    /*@ Inv Assert exists conflict_budget_value learnt_budget_value
                     conflict_count_value (random_value : fp64),
          s == s@pre &&
          0 <= conflict_count_value &&
          solver_search_loop(
          s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M) *
          store(&nof_conflicts, int, conflict_budget_value) *
          store(&nof_learnts, int, learnt_budget_value) *
          store(&random_var_freq, double, random_value) *
          store(&conflictC, uint64, conflict_count_value)
     */
    /* symexec SIGSEGVs on a `for' loop that omits its CONDITION -- always --
       or that omits its UPDATE and actually iterates (omitting the init alone
       is safe).  This `while (1)' is the C-standard expansion of the original
       `for(;;)' (C11 6.8.5.3p1), so it is a transcription of the frozen
       upstream loop, not a change of behaviour. */
    while (1) {
        clause *confl;
        /*@ solver_search_loop(
              s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M)
            which implies exists (Mcur : msolver)
                                 (learnt_words : list Z)
                                 learnt_cap assigns_ptr,
          ms_cap(Mcur) == ms_cap(M) &&
          solver_search_reuse(M, Mcur) &&
              solver_propagation_inv(
                n, F, A_arr, PropagationStable(A_inst), Mcur) &&
              msolver_seed_shadow(Mcur) && ms_model(Mcur) == nil &&
              msat_fp32_positive_finite(ms_cla_decay(Mcur)) &&
              solver_rep_assigns_levels_at(
                s, Mcur, assigns_ptr, levels, search_wl) *
              veci_rep(&(learnt_clause), learnt_words, learnt_cap)
         */
        /*@ Given Mcur learnt_words learnt_cap assigns_ptr */
        /*@ solver_propagation_inv(
              n, F, A_arr, PropagationStable(A_inst), Mcur) &&
              msolver_seed_shadow(Mcur) &&
              msat_fp32_positive_finite(ms_cla_decay(Mcur)) &&
              solver_rep_assigns_levels_at(
                s, Mcur, assigns_ptr, levels, search_wl) *
              undef_data_at(&(confl), clause *)
            which implies
              solver_propagate_pre(
                s, &(confl), n, F, A_arr,
                PropagationStable(A_inst), Mcur, assigns_ptr, levels, search_wl)
         */
        int propagation_status = solver_propagate(s, &confl);

        if (propagation_status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) {
            /*@ ms_cap(Mcur) == ms_cap(M) &&
                  solver_search_reuse(M, Mcur) &&
                  propagation_status <= -2 &&
                  -2 <= propagation_status &&
                  ms_model(Mcur) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mcur)) &&
                  solver_propagate_post(
                  s, &confl, n, F, A_arr, PropagationStable(A_inst),
                  Mcur, assigns_ptr, levels,
                  propagation_status, search_wl)
                which implies exists (Mcap : msolver),
                  ms_cap(Mcap) == ms_cap(M) &&
                  solver_search_reuse(M, Mcap) &&
                  solver_internal_capacity_ready(
                    n, F, A_arr, A_inst, Mcap) &&
                  solver_rep_levels_wl_at(s, Mcap, search_wl, levels) *
                  data_at(&confl, 0) *
                  has_permission(&propagation_status)
             */
            veci_delete(&learnt_clause);
            return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
        }
        if (propagation_status == 0){
            // CONFLICT
            int blevel;

            /*@ ms_cap(Mcur) == ms_cap(M) &&
                  solver_search_reuse(M, Mcur) &&
                  propagation_status <= 0 &&
                  0 <= propagation_status &&
                  ms_model(Mcur) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mcur)) &&
                  solver_propagate_post(
                  s, &confl, n, F, A_arr, PropagationStable(A_inst),
                  Mcur, assigns_ptr, levels, propagation_status, search_wl)
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
                    s, Mconf, assigns_ptr, levels, search_wl) *
                  data_at(&confl, p) *
                  has_permission(&propagation_status)
             */
            /*@ Given Mconf p focus Cconf */
            /*@ solver_rep_assigns_levels_at(
                  s, Mconf, assigns_ptr, levels, search_wl)
                which implies
                  store(&(s->stats.conflicts), uint64, stats_conflicts(ms_stats(Mconf))) *
                  store(&(s->root_level), int, ms_root_level(Mconf)) *
                  veci_rep(&(s->trail_lim),
                           mt_lim(ms_core(Mconf)), ms_lim_cap(Mconf)) *
                  solver_search_conflict_frame_at(s, Mconf, levels, search_wl)
             */

#ifdef VERBOSEDEBUG
            printf(L_IND"**CONFLICT**\n", L_ind);
#endif
            s->stats.conflicts++; conflictC++;
            if (solver_dlevel(s) == s->root_level){
                /* A `which implies' rather than a bare `exists (Mrootconf :
                   msolver), ..' assertion, which would have to be DERIVED:
                   nothing refolds the freshly bumped `stats.conflicts' cell plus
                   `solver_search_conflict_frame_at' into
                   `solver_rep_levels_at' at a new msolver.  As a
                   `which implies' the obligation moves to Coq.  Note the
                   root-level test is spelled as two inequalities and stated
                   EXPLICITLY: a which-implies VC is isolated, so the ambient
                   path condition from the enclosing `if' is not available,
                   and `cnf_unsat' is exactly what needs it. */
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
                      veci_rep(&(s->trail_lim),
                               mt_lim(ms_core(Mconf)), ms_lim_cap(Mconf)) *
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
                return -MINISAT_QCP_NEGATIVE_ONE_MAGNITUDE;
            }

            veci_resize(&learnt_clause,0);
            /* The native conflict counter has already been incremented, so
               the analyzer entry cannot be the old Mconf record.  Name the
               exact stats-only projection here; unlike a bare existential,
               its model and semantic core are definitionally inherited from
               Mconf, while its `stats_conflicts` counter owns the live conflicts_now cell. */
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
                  veci_rep(&(s->trail_lim),
                           mt_lim(ms_core(Mconf)), ms_lim_cap(Mconf)) *
                  solver_search_conflict_frame_at(s, Mconf, levels, search_wl) *
                  veci_rep(&(learnt_clause),
                           sublist(0, 0, learnt_words), learnt_cap)
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
                    Manalyze, focus, Cconf, learnt_cap, search_wl)
             */
            /*@ Given Manalyze */
            solver_analyze(s, confl, &learnt_clause)
              /*@ where anz_n = n, anz_F = F, anz_A_arr = A_arr,
                        K = PropagationStable(A_inst), M = Manalyze,
                        anz_focus = focus, C = Cconf,
                        anz_learnt_cap = learnt_cap,
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
                                     cap_after backjump,
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
                  veci_rep(&(learnt_clause), words, cap_after)
             */
            /*@ Given Manalyzed words cap_after backjump */
            /*@ solver_rep_levels_wl_at(s, Manalyzed, search_wl, levels)
                which implies
                  store(&(s->root_level), int,
                        ms_root_level(Manalyzed)) *
                  veci_rep(&(s->trail_lim),
                           mt_lim(ms_core(Manalyzed)),
                           ms_lim_cap(Manalyzed)) *
                  store(&(s->levels), int *, levels) *
                  IntArray::seg(levels, 0, ms_size(Manalyzed),
                                mt_levels(ms_core(Manalyzed))) *
                  IntArray::undef_seg(
                    levels, ms_size(Manalyzed), ms_cap(Manalyzed)) *
                  solver_search_root_payload(s, Manalyzed, search_wl)
             */
            blevel = veci_size(&learnt_clause) > 1 ? levels[lit_var(veci_begin(&learnt_clause)[1])] : s->root_level;
            blevel = s->root_level > blevel ? s->root_level : blevel;
            /* Refold the focus opened above; the msolver is unchanged, so
               this is the exact inverse of that block. */
            /*@ store(&(s->root_level), int,
                      ms_root_level(Manalyzed)) *
                  veci_rep(&(s->trail_lim),
                           mt_lim(ms_core(Manalyzed)),
                           ms_lim_cap(Manalyzed)) *
                  store(&(s->levels), int *, levels) *
                  IntArray::seg(levels, 0, ms_size(Manalyzed),
                                mt_levels(ms_core(Manalyzed))) *
                  IntArray::undef_seg(
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
                  veci_rep(&(learnt_clause), words, cap_after)
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
            /* `ms_model(Mcur) == nil' is restated because the RHS's
               `solver_search_backjump_ready(.. Mcur Mback words)' ends in
               `ms_model Mback = ms_model Mcur' while everything
               the LHS knows pins `ms_model Mback' to nil through
               `ms_model(Manalyzed)'.  A which-implies VC is ISOLATED, so
               `Mcur' would otherwise arrive `forall'-bound and unconstrained.
               The fact holds from the loop-entry block above. */
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
                  veci_rep(&(learnt_clause), words, cap_after)
                which implies exists (Mback : msolver),
                  ms_cap(Mback) == ms_cap(M) &&
                  solver_search_reuse(M, Mback) &&
                  record_watch1_positive(Mback, words) &&
                  solver_search_backjump_ready(
                    n, F, A_arr, A_inst, Mcur, Mback, words) &&
                  msat_fp32_positive_finite(ms_cla_decay(Mback)) &&
                  1 <= Zlength(words) &&
                  solver_rep_levels_wl_at(s, Mback, search_wl, levels) *
                  veci_rep(&(learnt_clause), words, cap_after) *
                  has_permission(&blevel)
             */
            /*@ Given Mback */
            /*@ solver_search_backjump_ready(
                  n, F, A_arr, A_inst, Mcur, Mback, words) &&
                  1 <= Zlength(words) &&
                  solver_rep_levels_wl_at(s, Mback, search_wl, levels) *
                  veci_rep(&(learnt_clause), words, cap_after)
                which implies
                  solver_record_pre_at(
                    s, &(learnt_clause), levels, n, F, A_arr, A_inst,
                    Mback, words, cap_after, search_wl)
             */
            if (solver_record(s, &learnt_clause)
                  /*@ where levels_ptr = levels, rec_wl = search_wl, rec_n = n, rec_F = F,
                            rec_A_arr = A_arr, rec_A_inst = A_inst,
                            M = Mback, rec_words = words,
                            words_cap = cap_after */ ==
                -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) {
                /* `solver_record' is called inside the `if' test, so its
                   return value has no C local and is unnameable.  An LHS
                   `exists' binder unifies with it spatially, and the value is
                   pinned with two INEQUALITIES -- an `==' would rewrite the
                   binder to the literal before the spatial match. */
                /*@ exists record_status,
                      ms_cap(Mback) == ms_cap(M) &&
                      solver_search_reuse(M, Mback) &&
                      record_watch1_positive(Mback, words) &&
                      record_status <= -2 &&
                      -2 <= record_status &&
                      ms_model(Mback) == nil &&
                      solver_record_post_at(
                      s, &(learnt_clause), levels, n, F, A_arr, A_inst,
                      Mback, words, cap_after, record_status, search_wl)
                    which implies exists (Mrecord_cap : msolver),
                      ms_cap(Mrecord_cap) == ms_cap(M) &&
                      solver_search_reuse(M, Mrecord_cap) &&
                      solver_internal_capacity_ready(
                        n, F, A_arr, A_inst, Mrecord_cap) &&
                      ms_model(Mrecord_cap) == nil &&
                      solver_rep_levels_wl_at(
                        s, Mrecord_cap, search_wl, levels) *
                      veci_rep(&(learnt_clause), words, cap_after)
                 */
                veci_delete(&learnt_clause);
                return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
            }
            /*@ exists record_status,
                  ms_cap(Mback) == ms_cap(M) &&
                  solver_search_reuse(M, Mback) &&
                  record_watch1_positive(Mback, words) &&
                  record_status != -2 &&
                  ms_model(Mback) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mback)) &&
                  solver_record_post_at(
                  s, &(learnt_clause), levels, n, F, A_arr, A_inst,
                  Mback, words, cap_after, record_status, search_wl)
                which implies exists (Mrecord : msolver),
                  ms_cap(Mrecord) == ms_cap(M) &&
                  solver_search_reuse(M, Mrecord) &&
                  msolver_inv(n, F, A_arr, A_inst, Mrecord) &&
                  ms_capacity_root_propagation_pending(Mrecord) == 0 &&
                  msolver_seed_shadow(Mrecord) &&
                  ms_model(Mrecord) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mrecord)) &&
                  solver_rep_levels_wl_at(s, Mrecord, search_wl, levels) *
                  veci_rep(&(learnt_clause), words, cap_after)
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

            /* A `which implies' rather than a bare `exists (Mdecay : msolver),
               ..' assertion.  The two decay calls leave `var_inc' and `cla_inc'
               at fresh heuristic values, and no library constructor updates
               those fields, so nothing can refold `solver_search_decay_frame_at'
               plus the four scalar cells back into `solver_rep_levels_at' at a
               new msolver.  As a `which implies' the record literal is written
               in Coq.  It folds straight to `solver_search_loop' so the
               `Assert' below only has to match one atom. */
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
                  veci_rep(&(learnt_clause), words, cap_after)
                which implies
                  solver_search_loop(
                    s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M)
             */
            /* `0 <= conflict_count_value' is pinned on EVERY full cut that
               binds that binder, not just on the loop invariant: an Assert
               destroys every fact it does not restate, so a partial pin would
               only relocate the defect to the loop back edge.  Here the value
               is the post-increment `unsigned_last_nbits(.. + 1, 64)', i.e. a
               `mod 2 ^ 64', which is nonnegative. */
            /*@ Assert exists conflict_budget_value learnt_budget_value
                         conflict_count_value (random_value : fp64),
                  s == s@pre &&
                  0 <= conflict_count_value &&
                  solver_search_loop(
                  s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M) *
                  store(&nof_conflicts, int, conflict_budget_value) *
                  store(&nof_learnts, int, learnt_budget_value) *
                  store(&random_var_freq, double, random_value) *
                  store(&conflictC, uint64, conflict_count_value) *
                  has_permission(&confl) *
                  has_permission(&propagation_status) *
                  has_permission(&blevel)
             */

        }else{
            // NO CONFLICT
            int next;

            /*@ ms_cap(Mcur) == ms_cap(M) &&
                  solver_search_reuse(M, Mcur) &&
                  propagation_status != 0 &&
                  propagation_status != -2 &&
                  ms_model(Mcur) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mcur)) &&
                  solver_propagate_post(
                  s, &confl, n, F, A_arr, PropagationStable(A_inst),
                  Mcur, assigns_ptr, levels, propagation_status, search_wl)
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
                    s, Mstable, assigns_ptr, levels, search_wl) *
                  data_at(&confl, 0) *
                  has_permission(&propagation_status)
             */
            /*@ Given Mstable */

            if (minisat_conflict_limit_reached(conflictC, nof_conflicts)){
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
                      veci_rep(&(s->trail_lim),
                        mt_lim(ms_core(Mprogress)),
                        ms_lim_cap(Mprogress)) *
                      solver_search_root_frame_at(
                        s, Mprogress, levels, search_wl)
                 */
                /* The argument read is hoisted into a temporary.
                   `solver_canceluntil' requires the opaque
                   `solver_cancel_pre(s, level, M, search_wl)', whose
                   `solver_cancel_owned' conjunct is `solver_nonlevel_rep',
                   which OWNS `s->root_level' (see solver_nonlevel_rep in
                   solver_qcp_lib.v).  The actual argument here IS
                   `s->root_level', so the cell must still be exposed when the
                   argument is evaluated, yet gone when the precondition is
                   checked -- and QCP offers no annotation point between those
                   two events.  C11 6.5.2.2p4 evaluates the argument before the
                   call, so a temporary for one lvalue read is exactly the
                   abstract-machine semantics, and it creates the annotation
                   point.  Neither alternative works: a strategy rule of rule
                   16's shape would have to `right_add' the opaque
                   `cancel_bound_ready(M, ms_root_level(M))' and a pure callee
                   `Require' is a hard stop; a second
                   `solver_canceluntil' spec (needs the search's ghosts in a
                   general-purpose contract plus a call-site selector).  DO NOT
                   "fix" this by producing the root_level cell on both sides of
                   the fold: that is a duplicated ownership claim and the VC
                   would be false. */
                int restart_root_level = s->root_level;
                /*@ msolver_inv(n, F, A_arr, A_inst, Mprogress) &&
                      mt_qhead(ms_core(Mprogress)) == ms_qtail(Mprogress) &&
                      msat_fp32_positive_finite(ms_cla_decay(Mprogress)) &&
                      store(&(s->root_level), int,
                            ms_root_level(Mprogress)) *
                      veci_rep(&(s->trail_lim),
                        mt_lim(ms_core(Mprogress)),
                        ms_lim_cap(Mprogress)) *
                      solver_search_root_frame_at(
                        s, Mprogress, levels, search_wl)
                    which implies
                      solver_cancel_pre(
                        s, ms_root_level(Mprogress), Mprogress, search_wl) *
                      solver_levels_slice_at(s, Mprogress, levels)
                 */
                solver_canceluntil(s,restart_root_level)
                  /*@ where M = Mprogress, wl = search_wl */;
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
                return MINISAT_QCP_ZERO_VALUE; }

            /*@ solver_rep_assigns_levels_at(
                  s, Mstable, assigns_ptr, levels, search_wl)
                which implies
                  store(&(s->root_level), int,
                        ms_root_level(Mstable)) *
                  veci_rep(&(s->trail_lim),
                    mt_lim(ms_core(Mstable)), ms_lim_cap(Mstable)) *
                  solver_search_root_frame_at(s, Mstable, levels, search_wl)
             */
            if (solver_dlevel(s) == 0) {
                int simplify_status;
                // Simplify the set of problem clauses:
                /* `solver_simplify_pre_at' is
                   `pure && solver_rep_levels_at', and its pure part is
                   exactly these four conjuncts (see solver_rep_levels_at in
                   solver_qcp_lib.v).  A which-implies
                   VC is ISOLATED, and the LHS spatial atoms say nothing about
                   n, F, A_arr or A_inst, so those have to be restated here;
                   with them the VC collapses to the same refold the
                   `solver_dlevel(s) != 0' arm below performs.  The
                   root-level test is spelled out for the same reason: the
                   ambient path condition from the enclosing `if' is not
                   available inside an isolated VC. */
                /*@ msolver_inv(n, F, A_arr, A_inst, Mstable) &&
                      Zlength(mt_lim(ms_core(Mstable))) == 0 &&
                      ms_capacity_root_propagation_pending(Mstable) == 0 &&
                      msolver_seed_shadow(Mstable) &&
                      store(&(s->root_level), int,
                          ms_root_level(Mstable)) *
                      veci_rep(&(s->trail_lim),
                        mt_lim(ms_core(Mstable)), ms_lim_cap(Mstable)) *
                      solver_search_root_frame_at(s, Mstable, levels, search_wl)
                    which implies A_inst == nil && ms_root_level(Mstable) == 0 &&
                      solver_simplify_pre_at(
                      s, n, F, A_arr, Mstable, levels, search_wl)
                 */
                /*@ solver_simplify_pre_at(s, n, F, A_arr, Mstable, levels, search_wl)
                    which implies solver_simplify_resumed_pre_at(
                      s, n, F, A_arr, Mstable, Mstable, levels, search_wl)
                 */
                simplify_status = solver_simplify(s)
                  /*@ where (solver_simplify_spec)
                            smp_n = n, smp_F = F, smp_A_arr = A_arr,
                            M = Mstable, smp_physical_entry = Mstable,
                            levels_ptr = levels, smp_wl = search_wl */;
                if (simplify_status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) {
                    /*@ A_inst == nil && ms_root_level(Mstable) == 0 &&
                      msolver_inv(n, F, A_arr, A_inst, Mstable) &&
                      Zlength(mt_lim(ms_core(Mstable))) == 0 &&
                      ms_cap(Mstable) == ms_cap(M) &&
          solver_search_reuse(M, Mstable) &&
          simplify_status <= -2 &&
                          -2 <= simplify_status &&
                          ms_model(Mstable) == nil &&
                          solver_simplify_post_at(
                          s, n, F, A_arr, Mstable, levels,
                          simplify_status, search_wl)
                        which implies exists (Msimplify_cap : msolver),
          ms_cap(Msimplify_cap) == ms_cap(M) &&
          solver_search_reuse(M, Msimplify_cap) &&
                          solver_internal_capacity_ready(
                            n, F, A_arr, A_inst, Msimplify_cap) &&
                          (minisat_watch_completed(Mstable) =>
                           minisat_watch_completed(Msimplify_cap)) &&
                          ms_model(Msimplify_cap) == nil &&
                          solver_rep_levels_wl_at(
                            s, Msimplify_cap, search_wl, levels) *
                          has_permission(&simplify_status)
                     */
                    veci_delete(&learnt_clause);
                    return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
                }
                if (simplify_status == 0) {
                    /*@ A_inst == nil && ms_root_level(Mstable) == 0 &&
                      msolver_inv(n, F, A_arr, A_inst, Mstable) &&
                      Zlength(mt_lim(ms_core(Mstable))) == 0 &&
                      ms_cap(Mstable) == ms_cap(M) &&
                          solver_search_reuse(M, Mstable) &&
                          simplify_status <= 0 &&
                          0 <= simplify_status &&
                          solver_simplify_post_at(
                          s, n, F, A_arr, Mstable, levels,
                          simplify_status, search_wl)
                        which implies exists (Msimplify_unsat : msolver),
                          ms_cap(Msimplify_unsat) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           solver_search_conflict_reuse(n, F, A_arr, A_inst, Msimplify_unsat)) &&
                          (minisat_watch_completed(Mstable) =>
                           solver_base_recovery(n, F, Msimplify_unsat) &&
                           msolver_seed_shadow(Msimplify_unsat)) &&
                          msolver_inv_weak(
                            n, F, A_arr, A_inst, Msimplify_unsat) &&
                          solver_at_root(Msimplify_unsat) &&
                          cancel_bound_ready(Msimplify_unsat, 0) &&
                          ms_capacity_root_propagation_pending(
                            Msimplify_unsat) == 0 &&
                          cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                          solver_rep_levels_wl_at(
                            s, Msimplify_unsat, search_wl, levels) *
                          has_permission(&simplify_status)
                     */
                    veci_delete(&learnt_clause);
                    return -MINISAT_QCP_NEGATIVE_ONE_MAGNITUDE;
                }
                /* Fall-through of the two early returns: `simplify_status' is
                   neither -2 nor 0, so `solver_simplify_post_at' is on its
                   `ret = 1' arm.  This has to be a `which implies' because a
                   top-level `||' inside the post is a PATH SPLIT at symexec
                   time -- the disjunction can only be resolved in Coq.
                   The entry empty-model and positive-decay facts are
                   restated on the LHS because this VC is ISOLATED and the
                   post preserves those properties conditionally. `has_permission(
                   &simplify_status)' restores the cell that naming
                   `simplify_status' as a value term on the LHS consumes;
                   without it the block exit fails to remove the memory
                   permission of `simplify_status'. */
                /*@ A_inst == nil && ms_root_level(Mstable) == 0 &&
                      msolver_inv(n, F, A_arr, A_inst, Mstable) &&
                      Zlength(mt_lim(ms_core(Mstable))) == 0 &&
                      ms_cap(Mstable) == ms_cap(M) &&
                      solver_search_reuse(M, Mstable) &&
                      simplify_status != -2 &&
                      simplify_status != 0 &&
                      ms_model(Mstable) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Mstable)) &&
                      solver_simplify_post_at(
                        s, n, F, A_arr, Mstable, levels,
                        simplify_status, search_wl)
                    which implies exists (Msimplify : msolver),
                      ms_cap(Msimplify) == ms_cap(M) &&
                      solver_search_reuse(M, Msimplify) &&
                      msolver_inv(n, F, A_arr, A_inst, Msimplify) &&
                      mt_qhead(ms_core(Msimplify)) == ms_qtail(Msimplify) &&
                      ms_capacity_root_propagation_pending(Msimplify) == 0 &&
                      msolver_seed_shadow(Msimplify) &&
                      ms_model(Msimplify) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Msimplify)) &&
                      solver_rep_levels_wl_at(s, Msimplify, search_wl, levels) *
                      has_permission(&simplify_status)
                 */
            } else {
                /* The `solver_dlevel(s) != 0' arm only has to REFOLD what the
                   unfold above opened for the `solver_dlevel' call -- the same
                   lemma instance as the accepted refold at the top of this
                   function.  Without this arm the join assertion below would
                   have to be derived from the raw cells on one path and from
                   `solver_simplify_post_at' on the other. */
                /*@ store(&(s->root_level), int,
                          ms_root_level(Mstable)) *
                      veci_rep(&(s->trail_lim),
                        mt_lim(ms_core(Mstable)), ms_lim_cap(Mstable)) *
                      solver_search_root_frame_at(s, Mstable, levels, search_wl)
                    which implies solver_rep_levels_wl_at(s, Mstable, search_wl, levels)
                 */
            }

            /*@ exists (Mclean : msolver),
                  ms_cap(Mclean) == ms_cap(M) &&
                  solver_search_reuse(M, Mclean) &&
                  msolver_inv(n, F, A_arr, A_inst, Mclean) &&
                  mt_qhead(ms_core(Mclean)) == ms_qtail(Mclean) &&
                  ms_capacity_root_propagation_pending(Mclean) == 0 &&
                  msolver_seed_shadow(Mclean) && ms_model(Mclean) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mclean)) &&
                  solver_rep_levels_wl_at(s, Mclean, search_wl, levels) *
                  veci_rep(&(learnt_clause),
                           learnt_words, learnt_cap)
             */
            /*@ Given Mclean */

            /*@ solver_rep_levels_wl_at(s, Mclean, search_wl, levels)
                which implies
                  store(&(s->qtail), int, ms_qtail(Mclean)) *
                  vecp_rep(&(s->learnts),
                    db_words(ms_learnt(Mclean)),
                    ms_learnt_cap(Mclean)) *
                  solver_search_reducedb_frame_at(
                    s, Mclean, levels, search_wl)
             */
            if (nof_learnts >= 0 && vecp_size(&s->learnts) - s->qtail >= nof_learnts) {
                // Reduce the set of learnt clauses:
                /* `solver_reducedb_pre_at' is
                   `pure && solver_rep_levels_at', and its pure part is
                   exactly these four conjuncts (see solver_rep_levels_at in
                   solver_qcp_lib.v).  A which-implies
                   VC is ISOLATED, and the LHS spatial atoms say nothing about
                   n, F, A_arr or A_inst, so those four have to be restated
                   here; with them the VC collapses to the same refold the
                   skip arm below performs.  All four are in scope from the
                   join assertion above. */
                /*@ msolver_inv(n, F, A_arr, A_inst, Mclean) &&
                      mt_qhead(ms_core(Mclean)) == ms_qtail(Mclean) &&
                      ms_capacity_root_propagation_pending(Mclean) == 0 &&
                      msolver_seed_shadow(Mclean) &&
                      msat_fp32_positive_finite(ms_cla_decay(Mclean)) &&
                      store(&(s->qtail), int, ms_qtail(Mclean)) *
                      vecp_rep(&(s->learnts),
                        db_words(ms_learnt(Mclean)),
                        ms_learnt_cap(Mclean)) *
                      solver_search_reducedb_frame_at(
                        s, Mclean, levels, search_wl)
                    which implies solver_reducedb_pre_at(
                      s, levels, n, F, A_arr, A_inst, Mclean, search_wl)
                 */
                solver_reducedb(s);
                /* `solver_reducedb_post_at' is an opaque `EX M'' bundle, so
                   the join assertion below cannot be DERIVED from it -- the
                   spatial atom `solver_rep_levels_wl_at(s, ?, search_wl, levels)' has to be
                   released by a `which implies'.  `ms_model(Mclean) == nil' is
                   on the LHS because the post only states
                   `ms_model M' == ms_model Mclean' and the VC is isolated. */
                /*@ ms_cap(Mclean) == ms_cap(M) &&
                      solver_search_reuse(M, Mclean) &&
                      ms_model(Mclean) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Mclean)) &&
                      solver_reducedb_post_at(
                        s, levels, n, F, A_arr, A_inst, Mclean, search_wl)
                    which implies exists (Mreduced : msolver),
                      ms_cap(Mreduced) == ms_cap(M) &&
                      solver_search_reuse(M, Mreduced) &&
                      msolver_inv(n, F, A_arr, A_inst, Mreduced) &&
                      mt_qhead(ms_core(Mreduced)) == ms_qtail(Mreduced) &&
                      ms_capacity_root_propagation_pending(Mreduced) == 0 &&
                      msolver_seed_shadow(Mreduced) &&
                      ms_model(Mreduced) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Mreduced)) &&
                      solver_rep_levels_wl_at(s, Mreduced, search_wl, levels)
                 */
            } else {
                /* The skip arm only has to refold what the unfold above opened
                   for the `vecp_size' / `s->qtail' reads in the `if' test. */
                /*@ store(&(s->qtail), int, ms_qtail(Mclean)) *
                      vecp_rep(&(s->learnts),
                        db_words(ms_learnt(Mclean)),
                        ms_learnt_cap(Mclean)) *
                      solver_search_reducedb_frame_at(
                        s, Mclean, levels, search_wl)
                    which implies solver_rep_levels_wl_at(s, Mclean, search_wl, levels)
                 */
            }

            /*@ exists (Mdb : msolver),
                  ms_cap(Mdb) == ms_cap(M) &&
                  solver_search_reuse(M, Mdb) &&
                  msolver_inv(n, F, A_arr, A_inst, Mdb) &&
                  mt_qhead(ms_core(Mdb)) == ms_qtail(Mdb) &&
                  ms_capacity_root_propagation_pending(Mdb) == 0 &&
                  msolver_seed_shadow(Mdb) && ms_model(Mdb) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mdb)) &&
                  solver_rep_levels_wl_at(s, Mdb, search_wl, levels) *
                  veci_rep(&(learnt_clause),
                           learnt_words, learnt_cap)
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
            /* `msolver_seed_shadow(Mdb)' is restated on the LHS: the RHS
               asks for `1 <= seed_shadow <= 2147483646 &&
               ms_random_seed(Mdb) == Z_to_fp64(seed_shadow)', which is
               literally that predicate's body (see msolver_seed_shadow in
               solver_qcp_lib.v), and
               `solver_rep_levels_at' only carries `solver_shape' -- it says
               nothing about the seed.  A which-implies VC is ISOLATED, so the
               ambient PROP occurrence does not reach it -- the "seed_shadow
               vacuity risk". */
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
                  veci_rep(&(s->order),
                    ms_order(Mdb), ms_order_cap(Mdb)) *
                  solver_search_order_frame_at(
                    s, Mdb, levels, activity_ptr,
                    assigns_select, orderpos_ptr, search_wl)
             */
            /*@ Given activity_ptr assigns_select orderpos_ptr */
            s->stats.decisions++;
            /*@ Given select_seed_shadow from seed_shadow */
            next = order_select(s, random_var_freq)
              /*@ where seed_shadow = select_seed_shadow */;
            /*@ Given order_now from heap1
                      orderpos_now from orderpos1
                      seed_now from seed_value1
                      seed_shadow_now from seed_shadow1 */

            /* A `which implies' rather than a bare `exists (Mselected :
               msolver), ..' assertion.  Same class as the other msolver steps
               here: the state holds the raw cells `order_select' just rewrote
               and nothing refolds them into `solver_rep_levels_at' at a NEW
               msolver.  As a `which implies' the RHS is ASSUMED and the
               obligation becomes a Coq VC in which `Mselected' is the record
               literal `msolver_search_select Mdb ..'.  The LHS therefore
               lists every cell AND every pure fact the VC needs -- a
               which-implies VC is ISOLATED from the ambient PROP list.  The
               `stats.decisions' cell is spelled the way the state spells the
               `++', not as `search_decision_stats_update(..)': symexec has no
               congruence closure and that function is opaque to it.
               `veci_rep(&(learnt_clause), ..)' is on neither side because it
               is untouched here and stays framed. */
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
                  veci_rep(&(s->order), order_now, ms_order_cap(Mdb)) *
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

            if (next == -MINISAT_QCP_NEGATIVE_ONE_MAGNITUDE){
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
                /* Both restated conjuncts are fields of
                   `solver_search_model_ready', produced by the block just
                   above: `msolver_inv' carries `n = ms_size Mselected'
                   (field msw_size) and `ms_model Mselected = nil' is a field
                   of the bundle itself.  A which-implies VC is ISOLATED, so
                   the ambient occurrence does not reach it.  Without the
                   first, the RHS cell `s->size |-> n' is unrelated to the
                   LHS's `ms_size Mselected'; without the second, the RHS
                   `veci_rep(&(s->model), nil, ..)' is unrelated to the LHS's
                   `veci_rep(&(s->model), ms_model(Mselected), ..)'.  Both are
                   needed: pinning only the size leaves the VC false. */
                /*@ ms_size(Mselected) == n &&
                      ms_model(Mselected) == nil &&
                      solver_rep_levels_wl_at(s, Mselected, search_wl, levels)
                    which implies exists values_ptr model_cap,
                      store(&(s->size), int, n) *
                      store(&(s->assigns), lbool *, values_ptr) *
                      CharArray::seg(
                        values_ptr, 0, n,
                        mt_assigns(ms_core(Mselected))) *
                      CharArray::undef_seg(
                        values_ptr, n, ms_cap(Mselected)) *
                      veci_rep(&(s->model), nil, model_cap) *
                      solver_model_copy_frame_at(
                        s, Mselected, levels, search_wl)
                 */
                /*@ Given values_ptr */
                lbool* values = s->assigns;
                int i;
                /* `Zlength(model_words) == i && 0 <= i && i <= n' are
                   restated in the invariant below because `model_copy_progress'
                   is opaque to symexec.  Without them the `veci_push'
                   capacity-abort arm (size == cap > 2^30-1) is not refuted and
                   `check(.. == 1)' fails; with them
                   i = Zlength(model_words) = cap > 2^30-1 contradicts i < n
                   and 2*n <= INT_MAX by LIA. */
                /*@ Inv Assert exists (model_words : list Z) model_cap_now,
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
                      CharArray::undef_seg(
                        values, n, ms_cap(Mselected)) *
                      veci_rep(
                        &(s->model), model_words, model_cap_now) *
                      veci_rep(&(learnt_clause),
                               learnt_words, learnt_cap) *
                      solver_model_copy_frame_at(
                        s, Mselected, levels, search_wl) *
                      store(&nof_conflicts, int, nof_conflicts) *
                      store(&nof_learnts, int, nof_learnts) *
                      has_permission(&random_var_freq) *
                      has_permission(&conflictC) *
                      has_permission(&confl) *
                      has_permission(&propagation_status) *
                      has_permission(&next)
                 */
                for (i = 0; i < s->size; i++) {
                    /* An `Inv Assert exists' binder is NOT in scope inside the
                       loop body until it is re-bound with `Given' (the body
                       otherwise reports "Use of undeclared identifier
                       model_words").  Braces added so the two `Given's and the
                       focus block share the body with the `check'. */
                    /*@ Given model_words model_cap_now */
                    /*@ model_copy_progress(
                          n, Mselected, model_words, i) && i < n &&
                          CharArray::seg(
                            values, 0, n,
                            mt_assigns(ms_core(Mselected)))
                        which implies
                          store(pointer_offset(
                                  values, i, sizeof(char), char),
                                char,
                                Znth(i,
                                  mt_assigns(ms_core(Mselected)), 0)) *
                          CharArray::missing_i(
                            values, i, 0, n,
                            mt_assigns(ms_core(Mselected)))
                     */
                    check(veci_push(&s->model,(int)values[i]) == 1);
                }
                /* A `which implies' rather than a bare `exists (Mdone :
                   msolver), ..' assertion.  The state holds the raw model-copy
                   cells and nothing refolds them into
                   `solver_rep_assigns_levels_at' at a NEW msolver; as a
                   `which implies' the RHS is ASSUMED and `Mdone' becomes the
                   record literal `msolver_with_model Mselected ..' in the Coq
                   VC.  The explicit `i >= n' is the loop-exit fact;
                   `model_copy_progress' already supplies its matching upper
                   bound and the model length when the proof unfolds it.  `learnt_clause',
                   `random_var_freq', `conflictC', `confl',
                   `propagation_status' and `next' are untouched here and stay
                   framed, so neither side names them. */
                /*@ exists (model_words_now : list Z) model_cap_now,
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
                      CharArray::undef_seg(
                        values, n, ms_cap(Mselected)) *
                      veci_rep(&(s->model),
                               model_words_now, model_cap_now) *
                      solver_model_copy_frame_at(
                        s, Mselected, levels, search_wl)
                    which implies exists (Mdone : msolver)
                                         (model_words : list Z)
                                         model_cap_done,
                      ms_cap(Mdone) == ms_cap(M) &&
                      solver_search_reuse(M, Mdone) &&
                      model_copy_finish(
                        n, F, A_arr, A_inst, Mselected,
                        model_words, model_cap_done, Mdone) &&
                      solver_rep_assigns_levels_at(
                        s, Mdone, values, levels, search_wl) *
                      has_permission(&i)
                 */
                /*@ Given Mdone model_words model_cap_done */
                /*@ model_copy_finish(
                      n, F, A_arr, A_inst, Mselected,
                      model_words, model_cap_done, Mdone) &&
                      solver_rep_assigns_levels_at(
                        s, Mdone, values, levels, search_wl)
                    which implies
                      model_copy_finish(
                        n, F, A_arr, A_inst, Mselected,
                        model_words, model_cap_done, Mdone) &&
                      store(&(s->root_level), int,
                        ms_root_level(Mdone)) *
                      veci_rep(&(s->trail_lim),
                        mt_lim(ms_core(Mdone)), ms_lim_cap(Mdone)) *
                      solver_search_root_frame_at(s, Mdone, levels, search_wl) *
                      has_permission(&values)
                 */
                /* Second root-level hoist (model-found arm).
                   Same hoist as the restart arm above: `solver_cancel_pre'
                   OWNS `s->root_level', which is also this call's own
                   argument, so the read must happen while the cell is still
                   exposed.  C11 6.5.2.2p4 makes the temporary exact. */
                int model_root_level = s->root_level;
                /*@ model_copy_finish(
                      n, F, A_arr, A_inst, Mselected,
                      model_words, model_cap_done, Mdone) &&
                      store(&(s->root_level), int,
                        ms_root_level(Mdone)) *
                      veci_rep(&(s->trail_lim),
                        mt_lim(ms_core(Mdone)), ms_lim_cap(Mdone)) *
                      solver_search_root_frame_at(s, Mdone, levels, search_wl)
                    which implies
                      model_copy_finish(
                        n, F, A_arr, A_inst, Mselected,
                        model_words, model_cap_done, Mdone) &&
                      solver_cancel_pre(
                        s, ms_root_level(Mdone), Mdone, search_wl) *
                      solver_levels_slice_at(s, Mdone, levels)
                 */
                solver_canceluntil(s,model_root_level)
                  /*@ where M = Mdone */;
                /*@ ms_cap(Mdone) == ms_cap(M) &&
                      solver_search_reuse(M, Mdone) &&
                      ms_cap(Mselected) == ms_cap(M) &&
                      solver_search_reuse(M, Mselected) &&
          model_copy_finish(
                      n, F, A_arr, A_inst, Mselected,
                      model_words, model_cap_done, Mdone) &&
                      solver_cancel_post(
                      s, ms_root_level(Mdone), Mdone, search_wl) *
                      solver_levels_slice_at(s, Mdone, levels) *
                      veci_rep(&(learnt_clause),
                               learnt_words, learnt_cap)
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
                      veci_rep(&(learnt_clause),
                               learnt_words, learnt_cap)
                 */
                veci_delete(&learnt_clause);

                /*
                veci apa; veci_new(&apa);
                for (i = 0; i < s->size; i++)
                    check(veci_push(&apa,(int)(s->model.ptr[i] == l_True ? toLit(i) : lit_neg(toLit(i)))) == 1);
                printf("model: "); printlits((lit*)apa.ptr, (lit*)apa.ptr + veci_size(&apa)); printf("\n");
                veci_delete(&apa);
                */

                return MINISAT_QCP_ONE_VALUE;
            }

            /*@ solver_search_select_transition(
                  n, F, A_arr, A_inst, Mdb, next,
                  orderpos_after, order_after,
                  seed_after, stats_after, Mselected) &&
                  next != -1
                which implies solver_search_selection_state(
                  n, F, A_arr, A_inst, next, Mselected)
             */
            /* The seven `decision_* == ms_*(Mselected)' ALIASES were
               deleted and every use re-spelled on the right-hand terms.
               The aliases cost a defect: the `assume' Ensure then spells
               `assume_post_at' on the alias ghosts, and the consuming
               which-implies VC is ISOLATED -- the alias equations are
               ambient PROP, not VC hypotheses, so the ghosts arrive
               `forall'-bound and unrelated to `Mselected'.  Restating the
               equations on the consuming LHS is not an escape either: an
               `==' rewrites its variable inside that LHS's own spatial
               atoms and the `assume_post_at' match then fails. */
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
                    mt_lim(ms_core(Mselected)),
                    ms_lim_cap(Mselected)) *
                  solver_assume_frame_wl(s, Mselected, search_wl)
             */
            /*@ Given decision_asg */
            assume(s,lit_neg(toLit(next)) /*@ where (original) */);
            /* A `which implies' rather than a bare `exists (Mdecision :
               msolver), ..' assertion; same class as the other msolver steps
               in this function.  `decision_lit' is an LHS
               existential because the enqueued literal is the value of a
               NESTED call (`lit_neg(toLit(next))') and is therefore unnameable
               -- the SPATIAL matcher does not unfold `retval == lit_neg_c(..)',
               so the atom can only be matched by a binder.  The
               binder is pinned with TWO INEQUALITIES, not `==': an `=='  would
               rewrite it inside this LHS's own `assume_post_at' and break that
               match.  The pure solver DOES have congruence (it discharged
               `assume's own `l == l0' Require the same way), so both
               inequalities are derivable, and `lia' recovers the equality in
               the isolated VC. */
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
                    mt_lim(ms_core(Mselected)),
                    ms_lim_cap(Mselected)) *
                  solver_assume_frame_wl(s, Mselected, search_wl)
                which implies exists (Mdecision : msolver) lim_cap_after,
                  ms_cap(Mdecision) == ms_cap(M) &&
                  solver_search_reuse(M, Mdecision) &&
                  solver_search_decision_transition(
                    n, F, A_arr, A_inst,
                    Mselected, next, lim_cap_after, Mdecision) &&
                  msat_fp32_positive_finite(ms_cla_decay(Mdecision)) &&
                  solver_rep_levels_wl_at(s, Mdecision, search_wl, levels)
             */
            /*@ Assert exists conflict_budget_value learnt_budget_value
                         conflict_count_value (random_value : fp64),
                  s == s@pre &&
                  0 <= conflict_count_value &&
                  solver_search_loop(
                  s, &(learnt_clause), levels,
                  n, F, A_arr, A_inst, search_wl, M) *
                  store(&nof_conflicts, int, conflict_budget_value) *
                  store(&nof_learnts, int, learnt_budget_value) *
                  store(&random_var_freq, double, random_value) *
                  store(&conflictC, uint64, conflict_count_value) *
                  has_permission(&confl) *
                  has_permission(&propagation_status) *
                  has_permission(&next)
             */
        }
    }

    return MINISAT_QCP_ZERO_VALUE; // cannot happen
}

//=================================================================================================
// External solver functions:

/* Allocate a solver with empty vectors, null per-variable arrays and zeroed
   counters, allocate its two-literal `binary' clause, and set the search
   heuristics to their default parameters. */
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
        undef_data_at(&(s->capacity_pending_qhead), int) *
        undef_data_at(&(s->capacity_root_propagation_pending), int) *
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
        undef_data_at(&(s->clauses.size), int) *
        undef_data_at(&(s->clauses.cap), int) *
        undef_data_at(&(s->clauses.ptr), void **) *
        undef_data_at(&(s->learnts.size), int) *
        undef_data_at(&(s->learnts.cap), int) *
        undef_data_at(&(s->learnts.ptr), void **) *
        undef_data_at(&(s->order.size), int) *
        undef_data_at(&(s->order.cap), int) *
        undef_data_at(&(s->order.ptr), int *) *
        undef_data_at(&(s->trail_lim.size), int) *
        undef_data_at(&(s->trail_lim.cap), int) *
        undef_data_at(&(s->trail_lim.ptr), int *) *
        undef_data_at(&(s->tagged.size), int) *
        undef_data_at(&(s->tagged.cap), int) *
        undef_data_at(&(s->tagged.ptr), int *) *
        undef_data_at(&(s->stack.size), int) *
        undef_data_at(&(s->stack.cap), int) *
        undef_data_at(&(s->stack.ptr), int *) *
        undef_data_at(&(s->model.size), int) *
        undef_data_at(&(s->model.cap), int) *
        undef_data_at(&(s->model.ptr), int *) *
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
    s->capacity_pending_qhead = 0;
    s->capacity_root_propagation_pending = 0;
    s->cla_inc                = 1;
    s->cla_decay              = 1;
    s->var_inc                = 1;
    s->var_decay              = 1;
    s->root_level             = 0;
    s->simpdb_assigns         = 0;
    s->simpdb_props           = 0;
    s->random_seed            = 91648253;
    s->progress_estimate      = 0;
    s->binary                 = minisat_clause_alloc(2);
    /*@ MiniSatClause::undef(s->binary, 2)
        which implies
          0 < s->binary && s->binary % 2 == 0 &&
          undef_data_at(&(s->binary->size_learnt), int) *
          undef_data_at(&(s->binary->activity), float) *
          IntArray::undef_seg(&(s->binary->lits), 0, 2)
     */
    s->binary->size_learnt    = (2 << 1);
    s->binary->lits[0]        = 0;
    s->binary->lits[1]        = 0;
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
          store(&(s->capacity_pending_qhead), int, 0) *
          store(&(s->capacity_root_propagation_pending), int, 0) *
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
          store(&(s->clauses.size), int, 0) *
          store(&(s->clauses.cap), int, 4) *
          store(&(s->clauses.ptr), void **, s->clauses.ptr) *
          PtrArray::seg(s->clauses.ptr, 0, 0, nil) *
          PtrArray::undef_seg(s->clauses.ptr, 0, 4) *
          store(&(s->learnts.size), int, 0) *
          store(&(s->learnts.cap), int, 4) *
          store(&(s->learnts.ptr), void **, s->learnts.ptr) *
          PtrArray::seg(s->learnts.ptr, 0, 0, nil) *
          PtrArray::undef_seg(s->learnts.ptr, 0, 4) *
          store(&(s->order.size), int, 0) *
          store(&(s->order.cap), int, 4) *
          store(&(s->order.ptr), int *, s->order.ptr) *
          IntArray::seg(s->order.ptr, 0, 0, nil) *
          IntArray::undef_seg(s->order.ptr, 0, 4) *
          store(&(s->trail_lim.size), int, 0) *
          store(&(s->trail_lim.cap), int, 4) *
          store(&(s->trail_lim.ptr), int *, s->trail_lim.ptr) *
          IntArray::seg(s->trail_lim.ptr, 0, 0, nil) *
          IntArray::undef_seg(s->trail_lim.ptr, 0, 4) *
          store(&(s->tagged.size), int, 0) *
          store(&(s->tagged.cap), int, 4) *
          store(&(s->tagged.ptr), int *, s->tagged.ptr) *
          IntArray::seg(s->tagged.ptr, 0, 0, nil) *
          IntArray::undef_seg(s->tagged.ptr, 0, 4) *
          store(&(s->stack.size), int, 0) *
          store(&(s->stack.cap), int, 4) *
          store(&(s->stack.ptr), int *, s->stack.ptr) *
          IntArray::seg(s->stack.ptr, 0, 0, nil) *
          IntArray::undef_seg(s->stack.ptr, 0, 4) *
          store(&(s->model.size), int, 0) *
          store(&(s->model.cap), int, 4) *
          store(&(s->model.ptr), int *, s->model.ptr) *
          IntArray::seg(s->model.ptr, 0, 0, nil) *
          IntArray::undef_seg(s->model.ptr, 0, 4) *
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
          undef_data_at(&(((clause *)initial_binary_raw)->activity), float) *
          store(pointer_offset(&(((clause *)initial_binary_raw)->lits), 0, sizeof(int), int), int, 0) *
          store(pointer_offset(&(((clause *)initial_binary_raw)->lits), 1, sizeof(int), int), int, 0) *
          IntArray::undef_seg(&(((clause *)initial_binary_raw)->lits), 2, 2)
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


#ifdef MINISAT_QCP_NATIVE_RUNTIME
/* Free every problem and learnt clause, the vectors, the watch lists and the
   per-variable arrays, and then the solver itself. */
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
#endif


/* Restore the saved propagation cursor only when its pending flag is set.
   This changes qhead and the flag; it does not propagate or drain the queue. */
static void solver_resume_pending(solver *s)
/*@ With (resume_entry : msolver) (resume_lvl resume_wl : Z)
    Require solver_rep_levels_wl_at(s, resume_entry, resume_wl, resume_lvl)
    Ensure solver_rep_levels_wl_at(
             s, msolver_resume_pending(resume_entry), resume_wl, resume_lvl)
 */
{
    /*@ solver_rep_levels_wl_at(s, resume_entry, resume_wl, resume_lvl)
        which implies exists resume_asg,
          store(&(s->qhead), int, mt_qhead(ms_core(resume_entry))) *
          store(&(s->qtail), int, ms_qtail(resume_entry)) *
          store(&(s->capacity_pending_qhead), int,
                ms_capacity_pending_qhead(resume_entry)) *
          store(&(s->capacity_root_propagation_pending), int,
                ms_capacity_root_propagation_pending(resume_entry)) *
          veci_rep(&(s->trail_lim),
            mt_lim(ms_core(resume_entry)), ms_lim_cap(resume_entry)) *
          solver_resume_frame_at(
            s, resume_entry, resume_asg, resume_lvl, resume_wl)
     */
    /*@ Given resume_asg */
    if (s->capacity_root_propagation_pending == 1) {
        s->qhead = s->capacity_pending_qhead;
        s->capacity_root_propagation_pending = 0;
    }
}

/* Add the clause over the literals in [begin, endvar) to the problem.  Grows
   the solver to cover the largest variable, sorts the literals and drops the
   duplicated and the root-false ones, and skips the clause entirely when it is
   a tautology or already true.  Returns 1, 0 when the clause is empty or
   refutes the formula at the root, or -2 out of capacity.  The capacity consequence
   solver_addclause_capacity_base_state__api_reentry recovers the original
   formula and a reusable base state, with ownership of the actual input array.
   Retrying the original clause requires a valid saved or refilled range. */
int solver_addclause(solver* s, lit* begin, lit* endvar)
/*@ addclause_spec */
{
    /*@ solver_rep_growable(s, ac_physical_entry)
        which implies exists ac_resume_wl ac_resume_lvl,
          solver_rep_levels_wl_at(
            s, ac_physical_entry, ac_resume_wl, ac_resume_lvl) *
          wlists_undef(ac_resume_wl, 2 * ms_size(ac_physical_entry),
                       2 * ms_cap(ac_physical_entry))
     */
    /*@ Given ac_resume_wl ac_resume_lvl */
    solver_resume_pending(s)
      /*@ where resume_entry = ac_physical_entry,
                resume_lvl = ac_resume_lvl, resume_wl = ac_resume_wl */;
    /*@ ac_M == msolver_resume_pending(ac_physical_entry) &&
          solver_rep_levels_wl_at(
            s, msolver_resume_pending(ac_physical_entry),
            ac_resume_wl, ac_resume_lvl) *
          wlists_undef(ac_resume_wl, 2 * ms_size(ac_physical_entry),
                       2 * ms_cap(ac_physical_entry))
        which implies solver_rep_growable(s, ac_M)
     */


    lit *i,*j;
    int maxvar;
    int status;
    lbool* values;
    lit last;
    clause *c;
    lit l;

    if (begin == endvar) return MINISAT_QCP_ZERO_VALUE;

    /* begin != endvar and endvar = begin + |input|*4 force |input| >= 1.
       QCP does not derive that on its own: a zero-length IntArray::seg
       offers no readable cell, so *begin is rejected without this cut. */
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
    /*@ Inv Assert exists (sorted rest : list Z) k,
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
          has_permission(&j) * has_permission(&status) *
          has_permission(&values) * has_permission(&last) *
          has_permission(&c) * has_permission(&l)
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
        l = *i;
        maxvar = lit_var(l) /*@ where (original) */ > maxvar ? lit_var(l) /*@ where (original) */ : maxvar;
        /*@ Inv Assert exists (pre suf rest2 arr : list Z) p junk,
              Zlength(mt_lim(ms_core(ac_M))) == 0 &&
              s == s@pre && begin == begin@pre && endvar == endvar@pre &&
              0 <= p && p <= k && Zlength(pre) == p &&
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
              has_permission(&status) * has_permission(&values) *
              has_permission(&last) * has_permission(&c)
         */
        for (j = i; j > begin; j--) {
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
            if (*(j-1) <= l) break;
            /* Open the focus sandwich at p for the write; QCP's post-priority
               rule recloses it as IntArray::seg(.., replace_Znth(p, .., arr)).
               The read at p-1 is served by the seg directly. */
            /*@ 0 <= p && p < Zlength(ac_input) &&
                  Zlength(arr) == Zlength(ac_input) &&
                  IntArray::seg(begin, 0, Zlength(ac_input), arr)
                which implies
                  0 <= p && p < Zlength(ac_input) &&
                  Zlength(arr) == Zlength(ac_input) &&
                  store(pointer_offset(begin, p, sizeof(int), int),
                        int, Znth(p, arr, 0)) *
                  IntArray::missing_i(begin, p, 0, Zlength(ac_input), arr)
             */
            *j = *(j-1);
        }
        /*@ Given pre suf rest2 arr p */
        /* the insertion point: same sandwich, at the stop index */
        /*@ 0 <= p && p < Zlength(ac_input) &&
              Zlength(arr) == Zlength(ac_input) &&
              j == begin + p * sizeof(int) &&
              IntArray::seg(begin, 0, Zlength(ac_input), arr)
            which implies
              0 <= p && p < Zlength(ac_input) &&
              Zlength(arr) == Zlength(ac_input) &&
              j == begin + p * sizeof(int) &&
              store(pointer_offset(begin, p, sizeof(int), int),
                    int, Znth(p, arr, 0)) *
              IntArray::missing_i(begin, p, 0, Zlength(ac_input), arr)
         */
        *j = l;
    }
    status = solver_setnvars(s, maxvar+1)
             /*@ where (setnvars_spec)
                   sn_F = ac_F, sn_A_arr = ac_A_arr, sn_A_inst = ac_A_inst,
                   sn_M = ac_M, sn_root = 0 */;
    if (status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        return status;

    /* setnvars hands back solver_rep_growable(s, Mnew), which is OPAQUE: the
       store(&(s->assigns), ..) cell and the assigns array are inside it, so
       `values = s->assigns' cannot be executed through it.  Open it into the
       corpus's assigns-focus shape -- the same decomposition solver_solve's
       assume loop runs on -- which is also what the dedup loop's
       values[lit_var(l)] lookups need. */
    /* setnvars' Ensure is destructed at the call return, so its model is an
       anonymous existential -- a `which implies' on setnvars_post_at(..) finds
       nothing to match.  The corpus names such a model with `Assert exists'
       (solver_record does exactly this after its own clause_new call).
       Being a full CUT, this Assert must also restate the array and every
       local's permission. */
    /*@ Assert exists (Mnew : msolver) (sortedf : list Z) asg lvlp wlg,
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          1 <= Zlength(ac_input) &&
          status == 1 && 0 <= maxvar && maxvar < ac_n &&
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
          CharArray::undef_seg(asg, ms_size(Mnew), ms_cap(Mnew)) *
          solver_assigns_focus_frame_wl_at(s, Mnew, wlg, lvlp) *
          wlists_undef(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
          IntArray::seg(begin, 0, Zlength(ac_input), sortedf) *
          has_permission(&i) * has_permission(&j) *
          has_permission(&values) * has_permission(&last) *
          has_permission(&c) * has_permission(&l)
     */
    /*@ Given Mnew sortedf asg lvlp wlg */

    values = s->assigns;

    // delete duplicates
    last = -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    j = begin;
    /*@ Inv Assert exists (kept tail : list Z) k q,
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
          CharArray::undef_seg(asg, ms_size(Mnew), ms_cap(Mnew)) *
          solver_assigns_focus_frame_wl_at(s, Mnew, wlg, lvlp) *
          wlists_undef(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
          IntArray::seg(begin, 0, Zlength(ac_input), app(kept, tail)) *
          has_permission(&maxvar) * has_permission(&status) *
          has_permission(&c) * has_permission(&l)
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
        l = *i;
        lbool sig = !lit_sign(l);
        sig += sig - 1;
        /* focus the assigns array at lit_var(l) -- the same sandwich
           enqueue's body opens for its own indexed read of `values`. */
        /*@               0 <= lit_var_c(l) && lit_var_c(l) < ms_size(Mnew) &&
              Zlength(mt_assigns(ms_core(Mnew))) == ms_size(Mnew) &&
              CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew)))
            which implies
              0 <= lit_var_c(l) && lit_var_c(l) < ms_size(Mnew) &&
              Zlength(mt_assigns(ms_core(Mnew))) == ms_size(Mnew) &&
              store(pointer_offset(asg, lit_var_c(l), sizeof(char), char),
                    char, Znth(lit_var_c(l), mt_assigns(ms_core(Mnew)), 0)) *
              CharArray::missing_i(asg, lit_var_c(l), 0, ms_size(Mnew),
                                   mt_assigns(ms_core(Mnew)))
         */
        if (l == lit_neg(last) /*@ where (sentinel) */ || sig == values[lit_var(l)])
            return MINISAT_QCP_ONE_VALUE;   // tautology
        else if (l != last && values[lit_var(l)] == MINISAT_QCP_ZERO_VALUE) {
                /* the keep slot: same write sandwich as the sort, at q */
                /*@ 0 <= q && q < Zlength(ac_input) &&
                      Zlength(app(kept, tail)) == Zlength(ac_input) &&
                      j == begin + q * sizeof(int) &&
                      IntArray::seg(begin, 0, Zlength(ac_input),
                                    app(kept, tail))
                    which implies
                      0 <= q && q < Zlength(ac_input) &&
                      Zlength(app(kept, tail)) == Zlength(ac_input) &&
                      j == begin + q * sizeof(int) &&
                      store(pointer_offset(begin, q, sizeof(int), int),
                            int, Znth(q, app(kept, tail), 0)) *
                      IntArray::missing_i(begin, q, 0, Zlength(ac_input),
                                          app(kept, tail))
                 */
                *j = l;
                last = l;
                j++;
        }
    }

    /* Name the dedup loop's existentials for the exit block.  A bare `Given'
       does NOT work here (it makes symexec lose `begin''s own cell); the loop
       has ended, so this is the same `Assert exists' situation as after the
       setnvars call -- and, being a full cut, it restates the whole state. */
    /*@ Assert exists (kept tail : list Z) q,
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
          CharArray::undef_seg(asg, ms_size(Mnew), ms_cap(Mnew)) *
          solver_assigns_focus_frame_wl_at(s, Mnew, wlg, lvlp) *
          wlists_undef(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
          IntArray::seg(begin, 0, Zlength(ac_input), app(kept, tail)) *
          has_permission(&i) * has_permission(&maxvar) *
          has_permission(&status) * has_permission(&c) *
          has_permission(&l)
     */
    /*@ Given kept tail q */
    if (j == begin)          // empty clause
        return MINISAT_QCP_ZERO_VALUE;
    else if (j - begin == 1) { // unit clause
        /* The enqueue peel, transcribed from solver_record's own enqueue call:
           refold the assigns focus into enqueue's view of the solver.  The
           reason pointer is NOT a premise -- enqueue_input, defined in solver_qcp_lib.v, takes
           the `reasons' LIST, never the pointer -- so passing 0 costs nothing. */
        /*@ store(&(s->assigns), lbool *, asg) *
              CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew))) *
              CharArray::undef_seg(asg, ms_size(Mnew), ms_cap(Mnew)) *
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
                mt_lim(ms_core(Mnew)), ms_lim_cap(Mnew)) *
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
                     lim = mt_lim(ms_core(Mnew)),
                     lim_cap = ms_lim_cap(Mnew) */;
    }

    /* clause_new wants solver_rep_levels_at plus JUST the kept prefix of the
       array.  Refold the assigns focus and split the segment at Zlength(kept).
       This is the problem-clause instance of item C's generalised spec:
       cn_sel = 0, so solver_selected_is_learnt(0) = false and the cert it
       demands is problem_clause_pending_cert -- exactly the dedup invariant. */
    /*@ store(&(s->assigns), lbool *, asg) *
          CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew))) *
          CharArray::undef_seg(asg, ms_size(Mnew), ms_cap(Mnew)) *
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
    status = clause_new(s, begin, j, 0, &s->clauses, &c)
             /*@ where (clause_new_spec)
                   lvl = lvlp, cn_n = ms_size(Mnew), cn_F = ac_F,
                   cn_A_arr = ac_A_arr, cn_A_inst = ac_A_inst,
                   cn_M = Mnew, cn_words = kept, cn_sel = 0,
                   cn_wl = wlg, cn_root = 0 */;
    if (status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        /* clause_new hands `c' back as clause_out # Ptr |-> 0 on this arm;
           restate it as the local's own cell so the return can release it
           (solver_record does exactly this after its own clause_new call). */
        /*@ Assert exists (Mcap : msolver),
              s == s@pre && begin == begin@pre && endvar == endvar@pre &&
              status == -2 &&
              1 <= Zlength(ac_input) &&
              clause_new_capacity_failure_root(ms_size(Mnew), ac_F, ac_A_arr, ac_A_inst, Mnew, Mcap, kept, 0, 0) &&
              (minisat_watch_completed(ac_M) => minisat_watch_completed(Mcap)) &&
              Zlength(mt_lim(ms_core(Mcap))) == 0 &&
              ms_size(ac_M) <= ms_size(Mnew) && ms_cap(ac_M) <= ms_cap(Mnew) &&
              2 * ms_cap(Mnew) <= INT_MAX &&
              Zlength(kept) == q &&
              Zlength(app(kept, tail)) == Zlength(ac_input) &&
              store(&(c), clause *, 0) *
              solver_rep_levels_wl_at(s, Mcap, wlg, lvlp) *
              wlists_undef(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
              IntArray::seg(begin, 0, Zlength(kept), kept) *
              IntArray::seg(begin, Zlength(kept), Zlength(ac_input), tail) *
              has_permission(&i) * has_permission(&j) *
              has_permission(&maxvar) * has_permission(&values) *
              has_permission(&last) * has_permission(&l)
         */
        return status;

    /*@ Assert exists (Mclause : msolver) c_new,
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          status == 1 && 1 <= Zlength(ac_input) &&
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
          store(&(c), clause *, c_new) *
          solver_rep_levels_wl_at(s, Mclause, wlg, lvlp) *
          wlists_undef(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
          IntArray::seg(begin, 0, Zlength(kept), kept) *
          IntArray::seg(begin, Zlength(kept), Zlength(ac_input), tail) *
          has_permission(&i) * has_permission(&maxvar) *
          has_permission(&values) * has_permission(&last) *
          has_permission(&l)
     */
    /*@ Given Mclause */
    /* The two stats cells are already in the footprint -- stats_rep sits
       inside solver_nonlevel_rep_at -- but a WRITE needs them handed out.
       solver_search_bundle_at already carries the statistics half as an
       explicit parameter, so the hole costs no new payload spelling. */
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

    return MINISAT_QCP_ONE_VALUE;
}


/* Remove the clauses that are already satisfied at the root level.  Propagates
   first, then walks the problem and the learnt databases, deleting each clause
   that `clause_simplify` reports satisfied and that is not itself a reason,
   and compacting the rest.  Returns 1, 0 when propagation refutes the formula,
   or -2 out of capacity.  solver_simplify_capacity_base_state__api_reentry
   recovers the original formula and owned base state after -2, without a
   progress guarantee. */
int solver_simplify(solver* s)
/*@ solver_simplify_spec */
{
    /*@ solver_simplify_resumed_pre_at(
          s, smp_n, smp_F, smp_A_arr, smp_physical_entry, M, levels_ptr, smp_wl)
        which implies
          M == msolver_resume_pending(smp_physical_entry) &&
          msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, M) &&
          Zlength(mt_lim(ms_core(M))) == 0 &&
          Zlength(mt_lim(ms_core(msolver_resume_pending(smp_physical_entry)))) == 0 &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          solver_rep_levels_wl_at(s, smp_physical_entry, smp_wl, levels_ptr)
     */
    solver_resume_pending(s)
      /*@ where resume_entry = smp_physical_entry,
                resume_lvl = levels_ptr, resume_wl = smp_wl */;
    /*@ M == msolver_resume_pending(smp_physical_entry) &&
          msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, M) &&
          Zlength(mt_lim(ms_core(M))) == 0 &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          solver_rep_levels_wl_at(
            s, msolver_resume_pending(smp_physical_entry), smp_wl, levels_ptr)
        which implies solver_simplify_pre_at(
          s, smp_n, smp_F, smp_A_arr, M, levels_ptr, smp_wl)
     */

    clause *conflict;
    int propagation_status;
    clause** reasons;
    int type;

    /*@ solver_simplify_pre_at(
          s, smp_n, smp_F, smp_A_arr, M, levels_ptr, smp_wl)
        which implies exists assigns_entry,
          msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, M) &&
          Zlength(mt_lim(ms_core(M))) == 0 &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          veci_rep(&(s->trail_lim), mt_lim(ms_core(M)),
                   ms_lim_cap(M)) *
          solver_simplify_lim_frame_at(
            s, M, assigns_entry, levels_ptr, smp_wl)
     */
    /*@ Given assigns_entry */

    assert(solver_dlevel(s) == 0);

    /*@ veci_rep(&(s->trail_lim), mt_lim(ms_core(M)),
                 ms_lim_cap(M)) *
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
            s, M, assigns_prop, levels_ptr, smp_wl) *
          undef_data_at(&(conflict), clause *)
        which implies
          solver_propagate_pre(
            s, &(conflict), smp_n, smp_F, smp_A_arr, PropagationAssuming(smp_A_arr),
            M, assigns_prop, levels_ptr, smp_wl)
     */
    propagation_status = solver_propagate(s, &conflict);
    if (propagation_status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        /*@ Assert s == s@pre &&
              solver_simplify_post_at(
              s, smp_n, smp_F, smp_A_arr, M,
              levels_ptr, -2, smp_wl) *
              has_permission(&conflict) *
              has_permission(&propagation_status) *
              has_permission(&reasons) * has_permission(&type)
         */
        return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    if (propagation_status == 0)
        /*@ Assert s == s@pre &&
                   solver_simplify_post_at(
                     s, smp_n, smp_F, smp_A_arr, M, levels_ptr, 0, smp_wl) *
                   has_permission(&conflict) *
                   has_permission(&propagation_status) *
                   has_permission(&reasons) * has_permission(&type) */
        return 0;

    /*@ msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, M) &&
          Zlength(mt_lim(ms_core(M))) == 0 &&
          solver_propagate_post(
          s, &conflict, smp_n, smp_F, smp_A_arr, PropagationAssuming(smp_A_arr), M,
          assigns_prop, levels_ptr, propagation_status, smp_wl) &&
          propagation_status != 0 &&
          propagation_status != -2
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
            s, Mprop, assigns_prop, levels_ptr, smp_wl) *
          data_at(&conflict, 0) *
          has_permission(&propagation_status)
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
        /*@ Assert s == s@pre &&
                   solver_simplify_post_at(
                     s, smp_n, smp_F, smp_A_arr, M, levels_ptr, 1, smp_wl) *
                   has_permission(&conflict) *
                   has_permission(&propagation_status) *
                   has_permission(&reasons) * has_permission(&type) */
        return 1;

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
    /*@ Inv Assert s == s@pre &&
          solver_simplify_outer_loop(
          s, smp_n, smp_F, smp_A_arr, reasons, levels_ptr, type, M, smp_wl) *
          has_permission(&conflict) *
          has_permission(&propagation_status)
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
              vecp_rep(solver_selected_vec(s, type), words_type,
                       solver_selected_cap(type, Mtype)) *
              clause_db_rep(solver_selected_db(type, Mtype)) *
              store(&(s->assigns), lbool *, asg_type) *
              CharArray::seg(asg_type, 0, ms_size(Mtype),
                             mt_assigns(ms_core(Mtype))) *
              veci_rep(&(s->trail_lim), z_nil, ms_lim_cap(Mtype)) *
              solver_simplify_db_rest_at(
                s, type, Mtype, reasons, levels_ptr, smp_wl, asg_type)
         */
        vecp*    cs  = type ? &s->learnts : &s->clauses;
        /*@ cs == solver_selected_vec(s, type) */
        clause** cls = (clause**)vecp_begin(cs);

        int i, j;
        i = 0;
        /*@ Inv Assert exists Mcur (words : list Z) asg,
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
              vecp_rep_at(cs, cls, words, solver_selected_cap(type, Mcur)) *
              clause_db_rep(solver_selected_db(type, Mcur)) *
              store(&(s->assigns), lbool *, asg) *
              CharArray::seg(asg, 0, ms_size(Mcur),
                             mt_assigns(ms_core(Mcur))) *
              veci_rep(&(s->trail_lim), z_nil, ms_lim_cap(Mcur)) *
              solver_simplify_db_rest_at(
                s, type, Mcur, reasons, levels_ptr, smp_wl, asg) *
              has_permission(&conflict) *
              has_permission(&propagation_status)
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
                             ms_wm(Mcur), ms_wcaps(Mcur)) *
                  store(&(s->reasons), clause **, reasons) *
                  PtrArray::seg(reasons, 0, ms_size(Mcur),
                                ms_reason_words(Mcur)) *
                  PtrArray::undef_seg(reasons, ms_size(Mcur), ms_cap(Mcur)) *
                  store(clause_hdr_addr(words[i - 0]), int,
                        clause_hdr_word(co_learnt(co), Zlength(co_lits(co)))) *
                  activity_state(words[i - 0], co_learnt(co)) *
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
            if (reasons[lit_var(*clause_begin(cls[i]))] != cls[i] &&
                clause_simplify(s,cls[i])
                  /*@ where n = ms_size(Mcur), clause_words = co_lits(co),
                            assigns0 = mt_assigns(ms_core(Mcur)),
                            is_learnt = co_learnt(co),
                            assigns_ptr = asg,
                            lim_cap = ms_lim_cap(Mcur) */
                  == MINISAT_QCP_ONE_VALUE) {
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
                      PtrArray::undef_seg(reasons, ms_size(Mcur),
                                          ms_cap(Mcur)) *
                      solver_wlists_handle(s, smp_wl) *
                      wlists_rep(smp_wl, ms_size(Mcur),
                                 ms_wm(Mcur), ms_wcaps(Mcur)) *
                      store(clause_hdr_addr(words[i - 0]), int,
                            clause_hdr_word(co_learnt(co),
                                            Zlength(co_lits(co)))) *
                      activity_state(words[i - 0], co_learnt(co)) *
                      IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                                    Zlength(co_lits(co)), co_lits(co)) *
                      stats_rep(&(s->stats), ms_stats(Mcur))
                    which implies
                      db_lookup(solver_selected_db(type, Mcur),
                                words[i - 0], co) &&
                      clause_remove_pre(
                      s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), smp_wl, reasons,
                      ms_wm(Mcur), ms_wcaps(Mcur), co_learnt(co),
                      co_lits(co), ms_stats(Mcur), ms_reason_words(Mcur))
                 */
                clause_remove(s,cls[i]);
                /*@ ms_cap(Mcur) == ms_cap(M) &&
                      ms_root_level(Mcur) == ms_root_level(M) &&
                      solver_simplify_reuse(M, Mcur) &&
                      msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mcur) &&
                      solver_simplify_db_compaction_inv(
                        type, Mcur, words, i, jcur) &&
                      jcur == j && 0 <= j && j <= i && i < Zlength(words) &&
                      clause_simplify_result(co_lits(co),
                                             mt_assigns(ms_core(Mcur)), 1) &&
                      Zlength(mt_lim(ms_core(Mcur))) == 0 &&
                      mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
                      ms_capacity_root_propagation_pending(Mcur) == 0 &&
                      msolver_seed_shadow(Mcur) &&
                      db_lookup(solver_selected_db(type, Mcur),
                                words[i - 0], co) &&
                      clause_remove_post(
                        s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), smp_wl,
                        reasons, ms_wm(Mcur), ms_wcaps(Mcur), co_lits(co),
                        ms_stats(Mcur), ms_reason_words(Mcur)) *
                      clause_db_pair_remainder(
                        solver_selected_prob_db(type, Mcur),
                        solver_selected_learnt_db(type, Mcur),
                        words[i - 0], co_learnt(co), co_lits(co)) *
                      vecp_rep_at(cs, cls, words,
                                  solver_selected_cap(type, Mcur)) *
                      store(&(s->assigns), lbool *, asg) *
                      CharArray::seg(asg, 0, ms_size(Mcur),
                                     mt_assigns(ms_core(Mcur))) *
                      veci_rep(&(s->trail_lim), z_nil, ms_lim_cap(Mcur)) *
                      solver_simplify_clause_frame_at(
                        s, type, Mcur, asg, levels_ptr)
                    which implies exists Mnext,
                      ms_cap(Mnext) == ms_cap(M) &&
                      ms_root_level(Mnext) == ms_root_level(M) &&
                      solver_simplify_reuse(M, Mnext) &&
                      solver_simplify_compaction_step(
                        smp_n, smp_F, smp_A_arr, type, Mcur, words,
                        i, jcur, Mnext, words, j) &&
                      vecp_rep_at(cs, cls, words,
                                  solver_selected_cap(type, Mnext)) *
                      clause_db_rep(solver_selected_db(type, Mnext)) *
                      store(&(s->assigns), lbool *, asg) *
                      CharArray::seg(asg, 0, ms_size(Mnext),
                                     mt_assigns(ms_core(Mnext))) *
                      veci_rep(&(s->trail_lim), z_nil, ms_lim_cap(Mnext)) *
                      solver_simplify_db_rest_at(
                        s, type, Mnext, reasons, levels_ptr, smp_wl, asg)
                 */
            }
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
                      store(&(cs->size), int, Zlength(words)) *
                      store(&(cs->cap), int,
                            solver_selected_cap(type, Mcur)) *
                      store(&(cs->ptr), void **, cls) *
                      PtrArray::full(cls, Zlength(words),
                                     replace_Znth(j, words[i - 0], words)) *
                      PtrArray::undef_seg(cls, Zlength(words),
                                          solver_selected_cap(type, Mcur)) *
                      clause_db_pair_remainder(
                        solver_selected_prob_db(type, Mcur),
                        solver_selected_learnt_db(type, Mcur),
                        words[i - 0], co_learnt(co), co_lits(co)) *
                      store(clause_hdr_addr(words[i - 0]), int,
                            clause_hdr_word(co_learnt(co),
                                            Zlength(co_lits(co)))) *
                      activity_state(words[i - 0], co_learnt(co)) *
                      IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                                    Zlength(co_lits(co)), co_lits(co)) *
                      store(&(s->size), int, ms_size(Mcur)) *
                      solver_wlists_handle(s, smp_wl) *
                      wlists_rep(smp_wl, ms_size(Mcur),
                                 ms_wm(Mcur), ms_wcaps(Mcur)) *
                      store(&(s->reasons), clause **, reasons) *
                      PtrArray::seg(reasons, 0, ms_size(Mcur),
                                    ms_reason_words(Mcur)) *
                      PtrArray::undef_seg(reasons, ms_size(Mcur),
                                          ms_cap(Mcur)) *
                      stats_rep(&(s->stats), ms_stats(Mcur)) *
                      solver_simplify_clause_frame_at(
                        s, type, Mcur, asg, levels_ptr)
                    which implies
                      solver_simplify_compaction_step(
                        smp_n, smp_F, smp_A_arr, type, Mcur, words,
                        i, j, Mcur,
                        solver_simplify_keep_words(words, i, j), j + 1) &&
                      0 <= j && j <= i && i < Zlength(words) &&
                      vecp_rep_at(cs, cls,
                                  solver_simplify_keep_words(words, i, j),
                                  solver_selected_cap(type, Mcur)) *
                      clause_db_rep(solver_selected_db(type, Mcur)) *
                      solver_simplify_db_rest_at(
                        s, type, Mcur, reasons, levels_ptr, smp_wl, asg)
                 */
                j++;
            }
            /*@ Assert exists Mnext (words_next : list Z),
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
                  vecp_rep_at(cs, cls, words_next,
                              solver_selected_cap(type, Mnext)) *
                  clause_db_rep(solver_selected_db(type, Mnext)) *
                  store(&(s->assigns), lbool *, asg) *
                  CharArray::seg(asg, 0, ms_size(Mnext),
                                 mt_assigns(ms_core(Mnext))) *
                  veci_rep(&(s->trail_lim), z_nil, ms_lim_cap(Mnext)) *
                  solver_simplify_db_rest_at(
                    s, type, Mnext, reasons, levels_ptr, smp_wl, asg) *
                  has_permission(&conflict) *
                  has_permission(&propagation_status)
             */
        }
        vecp_resize(cs,j);
        /*@ Assert s == s@pre &&
              solver_simplify_outer_loop(
              s, smp_n, smp_F, smp_A_arr,
              reasons, levels_ptr, type + 1, M, smp_wl) *
              has_permission(&conflict) *
              has_permission(&propagation_status) *
              has_permission(&cs) * has_permission(&cls) *
              has_permission(&i) * has_permission(&j)
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
    /* Recompute the simplification budget from the current problem and learnt literal counts. */
    s->simpdb_props = minisat_uint64_sum_to_int(
        s->stats.clauses_literals, s->stats.learnts_literals);

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
    return 1;
}


/* Solve the formula under the assumptions in [begin, endvar).  Drains the root
   propagation queue unconditionally on entry (`solver_resume_pending` followed by
   `solver_propagate`), so a queue left undrained by `solver_addclause`'s unit path
   -- or by an earlier capacity exit, which is only one of the ways it can be left
   undrained -- is propagated before any assumption is made; then assumes each
   literal in turn and runs restarts of `solver_search` with a growing conflict
   budget.  Returns 1 with a total assignment satisfying formula and assumptions, 0
   with the two together unsatisfiable, or -2 with a capacity-exhausted retry state
   and no SAT/UNSAT verdict.  A root-level conflict found by the entry drain returns
   0, and the formula alone is then unsatisfiable (cnf_unsat). */
int solver_solve(solver* s, lit* begin, lit* endvar)
/*@ solver_solve_spec */
{
    /* Entry drain.  The public Require is `solver_update_ready(n,F,nil,M)
       && solver_query_watch_ready(M)': M is the PHYSICAL record and the logical
       state is `msolver_resume_pending(M)'.  The seed propagates at entry (inside
       solver_search), so an undrained root queue left by solver_addclause -- whose
       unit path is `return enqueue(...)' -- must be propagated here, exactly as
       solver_simplify already does (c:11819-11908).  `solver_query_watch_ready(M)'
       is what makes the conflict arm's `solver_base_recovery' provable: it feeds
       the `minisat_base_watch_completed entry ->' gate in solver_propagate_post's
       ret=0 branch, which is the only route to a full watch frontier at Mconf. */
    /*@ solver_rep_wl(s, M, solve_wl)
        which implies exists levels_entry,
          solver_rep_levels_wl_at(s, M, solve_wl, levels_entry)
     */
    /*@ Given levels_entry */
    solver_resume_pending(s)
      /*@ where resume_entry = M, resume_lvl = levels_entry, resume_wl = solve_wl */;

    /* `conflict' and `propagation_status' live in a NESTED block, as they did in
       the block this replaces: the assumption loop below declares its own pair,
       and function-scope cells here would have to be accounted for by every
       assertion in the rest of the body. */
    {
        clause *conflict;
        int     propagation_status;

        /*@ solver_rep_levels_wl_at(
              s, msolver_resume_pending(M), solve_wl, levels_entry)
            which implies exists assigns_prop,
              solver_rep_assigns_levels_at(
                s, msolver_resume_pending(M), assigns_prop, levels_entry, solve_wl)
         */
        /*@ Given assigns_prop */

        /* `PropagationAssuming(nil)', not `PropagationStable(nil)': Stable is
           backed by `msolver_inv_weak', which needs `ms_root_level' information
           that `msolver_inv_assuming' deliberately omits and that
           `solver_update_ready' therefore cannot supply.  This mirrors
           simplify's entry bridge at c:11880-11887. */
        /*@ solver_update_ready(n, F, nil, M) &&
              msolver_seed_shadow(M) &&
              solver_rep_assigns_levels_at(
                s, msolver_resume_pending(M), assigns_prop, levels_entry, solve_wl) *
              undef_data_at(&(conflict), clause *)
            which implies
              solver_propagate_pre(
                s, &(conflict), n, F, nil, PropagationAssuming(nil),
                msolver_resume_pending(M), assigns_prop, levels_entry, solve_wl)
         */
        propagation_status = solver_propagate(s, &conflict);

        if (propagation_status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) {
            /*@ solver_update_ready(n, F, nil, M) &&
                  solver_query_watch_ready(M) &&
                  propagation_status <= -2 &&
                  -2 <= propagation_status &&
                  solver_propagate_post(
                    s, &conflict, n, F, nil, PropagationAssuming(nil),
                    msolver_resume_pending(M), assigns_prop, levels_entry,
                    propagation_status, solve_wl)
                which implies exists (Mdrain_cap : msolver),
                  ms_cap(Mdrain_cap) == ms_cap(M) &&
                  minisat_base_watch_completed(Mdrain_cap) &&
                  solver_prepare_capacity_pre(
                    s, n, F, nil, PropagationAssuming(nil), Mdrain_cap, solve_wl) *
                  data_at(&conflict, 0) *
                  has_permission(&propagation_status)
             */
            solver_prepare_public_capacity_exit(s);
            /*@ Assert s == s@pre && begin == begin@pre && endvar == endvar@pre &&
                  exists (Mcap : msolver),
                  assumptions_array(n, begin, endvar, A_arr) *
                  solver_capacity_arm_at(s, n, F, M, Mcap, solve_wl) *
                  has_permission(&conflict) *
                  has_permission(&propagation_status)
             */
            return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
        }
        if (propagation_status == 0) {
            /* Bare `return 0', mirroring simplify: no `solver_canceluntil(s, 0)'
               (a no-op at depth 0, c:2364-2394) and no `s->root_level = 0'.
               `propagation_caller_frame' preserves `ms_root_level' across
               propagation, so the UNWRITTEN root cell already matches the
               post-propagation ghost; writing 0 would desynchronise it from Mconf
               unless a `msolver_set_root' witness were carried.
               `assumptions_array' is on the LHS because `cnf_unsat' needs
               `Forall (literal_wf n) A_arr', and a `which implies' does not
               consume pure conjuncts. */
            /*@ solver_update_ready(n, F, nil, M) &&
                  solver_query_watch_ready(M) &&
                  propagation_status <= 0 &&
                  0 <= propagation_status &&
                  assumptions_array(n, begin, endvar, A_arr) *
                  solver_propagate_post(
                    s, &conflict, n, F, nil, PropagationAssuming(nil),
                    msolver_resume_pending(M), assigns_prop, levels_entry,
                    propagation_status, solve_wl)
                which implies exists (Mconf : msolver),
                  assumptions_array(n, begin, endvar, A_arr) *
                  solver_unsat_arm_at(s, n, F, A_arr, M, Mconf, solve_wl) *
                  has_permission(&conflict) *
                  has_permission(&propagation_status)
             */
            /*@ Assert s == s@pre && begin == begin@pre && endvar == endvar@pre &&
                  exists (Mconf : msolver),
                  assumptions_array(n, begin, endvar, A_arr) *
                  solver_unsat_arm_at(s, n, F, A_arr, M, Mconf, solve_wl) *
                  has_permission(&conflict) *
                  has_permission(&propagation_status)
             */
            return 0;
        }
        /*@ solver_update_ready(n, F, nil, M) &&
              solver_query_watch_ready(M) &&
              propagation_status != 0 &&
              propagation_status != -2 &&
              solver_propagate_post(
                s, &conflict, n, F, nil, PropagationAssuming(nil),
                msolver_resume_pending(M), assigns_prop, levels_entry,
                propagation_status, solve_wl)
            which implies exists (Mdrain_done : msolver),
              ms_cap(Mdrain_done) == ms_cap(M) &&
              solver_query_reuse(M, Mdrain_done) &&
              solver_query_ready(n, F, Mdrain_done) &&
              msolver_seed_shadow(Mdrain_done) &&
              solver_rep_wl(s, Mdrain_done, solve_wl) *
              has_permission(&conflict) *
              has_permission(&propagation_status)
         */
    }

    /*@ Assert s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          exists (Mdrained : msolver),
          ms_cap(Mdrained) == ms_cap(M) &&
          solver_query_reuse(M, Mdrained) &&
          solver_query_ready(n, F, Mdrained) &&
          msolver_seed_shadow(Mdrained) &&
          assumptions_array(n, begin, endvar, A_arr) *
          solver_rep_wl(s, Mdrained, solve_wl)
     */
    /*@ Given Mdrained */

    /* The entry decomposition now runs on the DRAINED state; it is the text the
       pre-fix body ran on M, with M replaced by Mdrained.  `values' is read after
       the drain because `solver_resume_pending' hides the assigns pointer
       existentially inside `solver_rep_levels_wl_at'. */
    /*@ solver_query_ready(n, F, Mdrained) &&
          msolver_seed_shadow(Mdrained) &&
          solver_rep_wl(s, Mdrained, solve_wl)
        which implies exists values_entry levels_done,
          solver_query_ready(n, F, Mdrained) &&
          msolver_seed_shadow(Mdrained) &&
          vecp_rep(
            &(s->clauses), db_words(ms_prob(Mdrained)), ms_prob_cap(Mdrained)) *
          store(&(s->assigns), lbool *, values_entry) *
          CharArray::seg(
            values_entry, 0, ms_size(Mdrained), mt_assigns(ms_core(Mdrained))) *
          CharArray::undef_seg(
            values_entry, ms_size(Mdrained), ms_cap(Mdrained)) *
          solver_solve_entry_rest_at(s, Mdrained, levels_done, solve_wl)
     */
    /*@ Given values_entry levels_done */
    double  nof_conflicts = 100;
    double  nof_learnts   = solver_nclauses(s)
                              /*@ where (solver_nclauses_spec) */ / 3;
    int     status        = MINISAT_QCP_ZERO_VALUE;
    lbool*  values        = s->assigns;
    lit*    i;

    /*@ vecp_rep(
          &(s->clauses), db_words(ms_prob(Mdrained)), ms_prob_cap(Mdrained)) *
          store(&(s->assigns), lbool *, values_entry) *
          CharArray::seg(
            values_entry, 0, ms_size(Mdrained), mt_assigns(ms_core(Mdrained))) *
          CharArray::undef_seg(
            values_entry, ms_size(Mdrained), ms_cap(Mdrained)) *
          solver_solve_entry_rest_at(s, Mdrained, levels_done, solve_wl)
        which implies
          solver_rep_assigns_levels_at(
            s, Mdrained, values_entry, levels_done, solve_wl)
     */

    /*@ Assert exists (Mready : msolver) levels_ptr,
          ms_cap(Mready) == ms_cap(M) &&
          solver_query_reuse(M, Mready) &&
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          solver_query_ready(n, F, Mready) &&
          msolver_seed_shadow(Mready) &&
          assumptions_array(n, begin, endvar, A_arr) *
          solver_rep_assigns_levels_at(
            s, Mready, values, levels_ptr, solve_wl) *
          store(&nof_conflicts, double, nof_conflicts) *
          store(&nof_learnts, double, nof_learnts) *
          store(&status, int, 0) *
          has_permission(&i)
     */
    /*@ Given Mready levels_ptr */

    //printf("solve: "); printlits(begin, endvar); printf("\n");
    /*@ solver_query_ready(n, F, Mready) &&
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
          mt_qhead(ms_core(Mready)) == ms_qtail(Mready) &&
          ms_capacity_root_propagation_pending(Mready) == 0 &&
          msolver_seed_shadow(Mready) &&
          store(&(s->assigns), lbool *, values) *
          CharArray::seg(
            values, 0, n, mt_assigns(ms_core(Mready))) *
          CharArray::undef_seg(values, n, ms_cap(Mready)) *
          IntArray::seg(begin, 0, Zlength(raw_entry), raw_entry) *
          solver_assigns_focus_frame_wl_at(
            s, Mready, solve_wl, levels_ptr)
     */
    /*@ Inv Assert exists (raw : list Z) (Mcur : msolver) k,
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
          mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
          ms_capacity_root_propagation_pending(Mcur) == 0 &&
          msolver_seed_shadow(Mcur) &&
          store(&(s->assigns), lbool *, values) *
          CharArray::seg(
            values, 0, n, mt_assigns(ms_core(Mcur))) *
          CharArray::undef_seg(values, n, ms_cap(Mcur)) *
          IntArray::seg(begin, 0, Zlength(raw), raw) *
          solver_assigns_focus_frame_wl_at(s, Mcur, solve_wl, levels_ptr) *
          store(&nof_conflicts, double, nof_conflicts) *
          store(&nof_learnts, double, nof_learnts) *
          store(&status, int, 0)
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
        /* The `k - 0' spellings above and below are NOT a typo.  This
           statement reads `*i' three times (lit_sign, lit_var, and the
           `assume' argument) and the reads are served directly out of
           `IntArray::seg(begin, 0, Zlength(raw), raw)', so symexec spells
           the loaded word as `Znth(k - lo, raw, 0)' with the segment's
           literal `lo = 0'.  The usual read-only focus sandwich cannot be
           used here: a post-priority rule recloses `store + missing_i' into
           `IntArray::seg(.., replace_Znth(k, Znth(k, raw, 0), raw))' before
           the C statement runs, which is a strictly worse respelling and
           also corrupts the second and third reads.  `k - 0 = k' by lia, so
           every VC below is definitional. */
        lbool assumption_status =
            lit_sign(*i)
              ? -values[lit_var(*i) /*@ where (bounded_index) lv_bound_n = n */]
              : values[lit_var(*i) /*@ where (bounded_index) lv_bound_n = n */];

        /*@ -1 <= assumption_status &&
                   assumption_status <= 1
         */

        if (assumption_status == MINISAT_QCP_ONE_VALUE)
            /* `assumption_status' is a C LOCAL: inside the ISOLATED
               which_implies_wit goal it is an unconstrained universal, so
               `assumption_status == 1' says nothing about the solver state and
               an RHS phrased over it is false.  The semantic content of the C ternary
               `lit_sign(*i) ? -values[lit_var(*i)] : values[lit_var(*i)] == 1'
               is exactly "the k-th assumption literal is TRUE on the trail",
               i.e. assigns[var] == lit_sig(lit) == 1 - 2*lit_sign_c(lit).
               That spelling is sign-independent, so it needs no `=>' guard and
               it is discharged on BOTH ternary paths from that path's own
               PreH (`retval = lit_sign_c(..)' plus the cast equation), using
               `signed_last_nbits x 8 = x' for the lbool cells x in {-1,0,1}.
               `Forall(lit_wf_c(n), raw)' is a loop-invariant conjunct,
               restated because a which_implies_wit sees no ambient PROPs. */
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
            continue;
        if (assumption_status == MINISAT_QCP_ZERO_VALUE) {
            clause *conflict;
            int propagation_status;

            /* As in the ONE_VALUE arm above: `assumption_status == 0' is an
               equation about a dead universal inside the isolated goal, and
               `assumption_fresh_ready' needs BOTH
               `Znth(lit_var_c(current), assigns, 0) == 0' (the cell is
               unassigned) AND `Zlength(mt_lim(ms_core(Mcur))) < n'.  The first
               is the semantic content of the C ternary reading 0 -- it is
               sign-INDEPENDENT here, since `-0 == 0'.  The second follows from
               the first: the unassigned variable is off the trail
               (`mtw_assigned_iff'), the trail variables are distinct
               (`mtw_trail_nodup') and all lie in [0, n), so the trail is at
               most n-1 long and `mt_lim' (strictly sorted inside the trail) is
               no longer than it. */
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
                  CharArray::undef_seg(values, n, ms_cap(Mcur)) *
                  solver_assigns_focus_frame_wl_at(s, Mcur, solve_wl, levels_ptr)
                which implies
                  assumption_fresh_ready(n, raw, k, Mcur) &&
                  store(&(s->qhead), int, ms_qtail(Mcur)) *
                  enqueue_state_at(
                    s, values, levels_ptr, n, ms_cap(Mcur),
                    ms_qtail(Mcur), mt_assigns(ms_core(Mcur)),
                    mt_levels(ms_core(Mcur)), ms_reason_words(Mcur),
                    mt_trail(ms_core(Mcur)), mt_lim(ms_core(Mcur)),
                    ms_lim_cap(Mcur)) *
                  solver_assume_frame_wl(s, Mcur, solve_wl)
             */
            assume(s, *i);
            /* Same class as D1.  `assumption_fresh_transition' asserts
               `solver_propagation_inv n F A_arr ... Mdecide', a closed
               semantic statement about F and A_arr, but `assume_post_at' and
               `solver_assume_frame' are purely physical: in the isolated VC
               `F' and `A_arr' were unconstrained universals and the goal was
               FALSE.  Every conjunct added below is a live loop-invariant (or
               pre-call) fact, restated because a which_implies_wit sees no
               ambient PROPs. */
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
                  mt_lim(ms_core(Mcur)), ms_lim_cap(Mcur)) *
                  solver_assume_frame_wl(s, Mcur, solve_wl)
                which implies exists lim_cap_next (Mdecide : msolver),
                  ms_cap(Mdecide) == ms_cap(M) &&
                  solver_query_reuse(M, Mdecide) &&
                  assumption_fresh_transition(
                    n, F, A_arr, raw, k, lim_cap_next,
                    Mcur, Mdecide) &&
                  solver_rep_assigns_levels_at(
                    s, Mdecide, values, levels_ptr, solve_wl)
             */
            /*@ Given lim_cap_next Mdecide */
            /*@ assumption_fresh_transition(
                  n, F, A_arr, raw, k, lim_cap_next, Mcur, Mdecide) &&
                  solver_rep_assigns_levels_at(
                    s, Mdecide, values, levels_ptr, solve_wl) *
                  undef_data_at(&(conflict), clause *)
                which implies
                  solver_propagate_pre(
                    s, &(conflict), n, F, A_arr,
                    PropagationAssuming(assumption_prefix(raw, k + 1)),
                    Mdecide, values, levels_ptr, solve_wl)
             */
            propagation_status = solver_propagate(s, &conflict);
            /* solver_propagate returns exactly {1, 0, -2}; spelled as an
               interval plus one exclusion because a top-level `||' in an
               assertion is a PATH SPLIT in QCP, not a disjunction. */
            /*@ solver_propagate_post(
                  s, &conflict, n, F, A_arr,
                  PropagationAssuming(assumption_prefix(raw, k + 1)),
                  Mdecide, values, levels_ptr, propagation_status, solve_wl)
                which implies
                  -2 <=
                    propagation_status &&
                  propagation_status <= 1 &&
                  propagation_status != -1 &&
                  solver_propagate_post(
                    s, &conflict, n, F, A_arr,
                    PropagationAssuming(assumption_prefix(raw, k + 1)),
                    Mdecide, values, levels_ptr, propagation_status, solve_wl)
             */
            if (propagation_status == 1)
                /*@ ms_cap(Mdecide) == ms_cap(M) &&
                      solver_query_reuse(M, Mdecide) &&
                      propagation_status <= 1 &&
                      1 <= propagation_status &&
                      solver_propagate_post(
                      s, &conflict, n, F, A_arr,
                      PropagationAssuming(assumption_prefix(raw, k + 1)),
                      Mdecide, values, levels_ptr, propagation_status, solve_wl)
                    which implies exists (Mprop : msolver),
                      ms_cap(Mprop) == ms_cap(M) &&
                      solver_query_reuse(M, Mprop) &&
                      assumption_propagation_success(
                        n, F, A_arr, raw, k + 1, Mprop) &&
                      solver_rep_assigns_levels_at(
                        s, Mprop, values, levels_ptr, solve_wl) *
                      data_at(&conflict, 0) *
                      has_permission(&propagation_status)
                 */
                /*@ Given Mprop */
                /* Same class as D1: the RHS states dimensional facts about
                   `n' that the physical LHS cannot supply -- `n' was an
                   unconstrained universal in the isolated VC.
                   `assumption_propagation_success' carries
                   `msolver_inv_assuming_strong', whose `msa_size' and
                   `msa_trail_wf' give the two `n' equalities; the two integer
                   bounds are loop-invariant conjuncts and are restated
                   because a which_implies_wit sees no ambient PROPs. */
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
                      CharArray::undef_seg(values, n, ms_cap(Mprop)) *
                      solver_assigns_focus_frame_wl_at(
                        s, Mprop, solve_wl, levels_ptr)
                 */
                continue;
            if (propagation_status == 0) {
                /*@ ms_cap(Mdecide) == ms_cap(M) &&
                      solver_query_reuse(M, Mdecide) &&
                      propagation_status <= 0 &&
                      0 <= propagation_status &&
                      solver_propagate_post(
                      s, &conflict, n, F, A_arr,
                      PropagationAssuming(assumption_prefix(raw, k + 1)),
                      Mdecide, values, levels_ptr, propagation_status, solve_wl)
                    which implies exists (Mconf : msolver) p focus
                                                (Cconf : clause),
                      ms_cap(Mconf) == ms_cap(M) &&
          (solver_query_reuse_guard(M) =>
           minisat_watch_conflict_ready(n, Mconf)) &&
                      minisat_resident_false_clause(Mconf) &&
                      msolver_seed_shadow(Mconf) &&
                      propagation_cancel_ready(
                        n, F, A_arr,
                        PropagationAssuming(
                          assumption_prefix(raw, k + 1)),
                        Mconf, focus) &&
                      propagation_conflict_cert(n, F, Mconf, Cconf) &&
                      conflict_ptr_denotes(Mconf, p, Cconf) &&
                      solver_rep_assigns_levels_at(
                        s, Mconf, values, levels_ptr, solve_wl) *
                      data_at(&conflict, p) *
                      has_permission(&propagation_status)
                 */
                /*@ Given Mconf p focus Cconf */
                /*@ propagation_cancel_ready(
                      n, F, A_arr,
                      PropagationAssuming(assumption_prefix(raw, k + 1)),
                      Mconf, focus) &&
                      propagation_conflict_cert(n, F, Mconf, Cconf) &&
                      conflict_ptr_denotes(Mconf, p, Cconf)
                    which implies
                      propagation_cancel_ready(
                        n, F, A_arr,
                        PropagationAssuming(
                          assumption_prefix(raw, k + 1)),
                        Mconf, focus) &&
                      ms_size(Mconf) == n &&
                      cnf_unsat(n, cnf_with_units(F, A_arr))
                 */
                /*@ propagation_cancel_ready(
                      n, F, A_arr,
                      PropagationAssuming(
                        assumption_prefix(raw, k + 1)),
                      Mconf, focus) &&
                      solver_rep_assigns_levels_at(
                        s, Mconf, values, levels_ptr, solve_wl)
                    which implies
                      solver_cancel_pre(s, 0, Mconf, solve_wl) *
                      solver_levels_slice_at(s, Mconf, levels_ptr) *
                      has_permission(&values)
                 */
                solver_canceluntil(s, 0);
                /* Same shape as the cancel block of the conflict-resume path
                   above: `solver_unsat_arm' unfolds to
                   `ms_size M = n /\ cnf_unsat n (cnf_with_units F A_arr)',
                   neither of which the two cancellation predicates can supply
                   (they take no `cnf' and no `n').  Both facts are live: the
                   semantic-export block above puts them on its RHS. */
                /*@ ms_cap(Mconf) == ms_cap(M) &&
          (solver_query_reuse_guard(M) =>
           minisat_watch_conflict_ready(n, Mconf)) &&
                      minisat_resident_false_clause(Mconf) &&
                      msolver_seed_shadow(Mconf) &&
                      ms_size(Mconf) == n &&
                      propagation_cancel_ready(n, F, A_arr,
                        PropagationAssuming(assumption_prefix(raw, k + 1)),
                        Mconf, focus) &&
                      cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                      solver_cancel_post(s, 0, Mconf, solve_wl) *
                      solver_levels_slice_at(s, Mconf, levels_ptr)
                    which implies exists (Massumption_unsat : msolver),
                      ms_cap(Massumption_unsat) == ms_cap(M) &&
                      solver_unsat_arm_at(
                        s, n, F, A_arr, M, Massumption_unsat, solve_wl)
                 */
                return 0;
            }
            if (propagation_status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) {
                /*@ propagation_status <= -2 &&
                      -2 <= propagation_status &&
                      solver_propagate_post(
                      s, &conflict, n, F, A_arr,
                      PropagationAssuming(assumption_prefix(raw, k + 1)),
                      Mdecide, values, levels_ptr, propagation_status, solve_wl)
                    which implies
                      solver_propagation_capacity_raw(
                        s, n, F, A_arr,
                        PropagationAssuming(
                          assumption_prefix(raw, k + 1)),
                        Mdecide, values, levels_ptr, solve_wl) *
                      data_at(&conflict, 0) *
                      has_permission(&propagation_status)
                 */
                /*@ ms_cap(Mdecide) == ms_cap(M) &&
          solver_query_reuse(M, Mdecide) &&
          solver_propagation_capacity_raw(
                      s, n, F, A_arr,
                      PropagationAssuming(assumption_prefix(raw, k + 1)),
                      Mdecide, values, levels_ptr, solve_wl)
                    which implies exists (Mcap : msolver),
          ms_cap(Mcap) == ms_cap(M) &&
          solver_query_reuse(M, Mcap) &&
                      solver_prepare_capacity_pre(
                        s, n, F, A_arr,
                        PropagationAssuming(
                          assumption_prefix(raw, k + 1)), Mcap, solve_wl) *
                      has_permission(&values)
                 */
                solver_prepare_public_capacity_exit(s);
                /*@ Assert s == s@pre && begin == begin@pre && endvar == endvar@pre &&
                      exists (Mcap : msolver),
                      assumptions_array(n, begin, endvar, A_arr) *
                      solver_capacity_arm_at(s, n, F, M, Mcap, solve_wl) *
                      has_permission(&nof_conflicts) *
                      has_permission(&nof_learnts) *
                      has_permission(&status) * has_permission(&values) *
                      has_permission(&i) *
                      has_permission(&assumption_status) *
                      has_permission(&conflict) *
                      has_permission(&propagation_status)
                 */
                return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
            }
        }
        if (assumption_status == -MINISAT_QCP_NEGATIVE_ONE_MAGNITUDE) {
            /* A false assumption contradicts the trail: the k-th literal is
               false, so its negation is already covered by the strong assuming
               invariant.  This establishes UNSAT for the formula with every
               public assumption; the semantic premises below remain explicit
               because the C return value alone does not establish that fact. */
            /*@ msolver_inv_assuming_strong(
                  n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
                  A_arr == assumption_prefix(raw, Zlength(raw)) &&
                  0 <= k && k < Zlength(raw) &&
                  Forall(lit_wf_c(n), raw) &&
                  Znth(lit_var_c(Znth(k, raw, 0)),
                       mt_assigns(ms_core(Mcur)), 0) ==
                    2 * lit_sign_c(Znth(k, raw, 0)) - 1 &&
                  assumption_status == -1
                which implies
                  msolver_inv_assuming_strong(
                    n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
                  cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                  has_permission(&assumption_status)
             */
            /*@ msolver_inv_assuming_strong(
                  n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
                  cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                  store(&(s->assigns), lbool *, values) *
                  CharArray::seg(
                    values, 0, n, mt_assigns(ms_core(Mcur))) *
                  CharArray::undef_seg(values, n, ms_cap(Mcur)) *
                  solver_assigns_focus_frame_wl_at(s, Mcur, solve_wl, levels_ptr)
                which implies
                  solver_cancel_pre(s, 0, Mcur, solve_wl) *
                  solver_levels_slice_at(s, Mcur, levels_ptr) *
                  has_permission(&values)
             */
            solver_canceluntil(s, 0);
            /* The UNSAT fact and size equality are restated because the
               cancellation resources carry neither the public CNF nor n. */
            /*@ ms_cap(Mcur) == ms_cap(M) &&
                  solver_query_reuse(M, Mcur) &&
                  ms_size(Mcur) == n &&
                  msolver_inv_assuming_strong(
                    n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
                  mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
                  ms_capacity_root_propagation_pending(Mcur) == 0 &&
                  msolver_seed_shadow(Mcur) &&
                  cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                  solver_cancel_post(s, 0, Mcur, solve_wl) *
                  solver_levels_slice_at(s, Mcur, levels_ptr)
                which implies exists (Mfalse_unsat : msolver),
                  ms_cap(Mfalse_unsat) == ms_cap(M) &&
                  solver_unsat_arm_at(s, n, F, A_arr, M, Mfalse_unsat, solve_wl)
             */
            return 0;
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
          CharArray::undef_seg(values, n, ms_cap(Mcur)) *
          solver_assigns_focus_frame_wl_at(s, Mcur, solve_wl, levels_ptr)
        which implies
          store(&(s->root_level), int, ms_root_level(Mcur)) *
          veci_rep(&(s->trail_lim),
                   mt_lim(ms_core(Mcur)), ms_lim_cap(Mcur)) *
          solver_root_install_frame_at(
            s, Mcur, values, levels_ptr, solve_wl)
     */
    s->root_level = solver_dlevel(s);
    /*@ ms_cap(Mcur) == ms_cap(M) &&
          solver_query_reuse(M, Mcur) &&
          msolver_inv_assuming_strong(n, F, A_arr, A_arr, Mcur) &&
          mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
          ms_capacity_root_propagation_pending(Mcur) == 0 &&
          msolver_seed_shadow(Mcur) &&
          store(&(s->root_level), int,
                Zlength(mt_lim(ms_core(Mcur)))) *
          veci_rep(&(s->trail_lim),
                   mt_lim(ms_core(Mcur)), ms_lim_cap(Mcur)) *
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

    /*@ Inv Assert s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          solver_restart_loop(
          s, begin, endvar, n, F, A_arr, status, solve_wl, M) *
          store(&nof_conflicts, double, nof_conflicts) *
          store(&nof_learnts, double, nof_learnts) *
          has_permission(&values) *
          has_permission(&i)
     */
    while (status == MINISAT_QCP_ZERO_VALUE){
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
        /* The frozen `(int)nof_conflicts` double-to-int casts are
           inexpressible in canonical QCP (see minisat_qcp_compat.h).  The native facade
           preserves defined nonnegative casts and saturates the otherwise undefined
           upper range; its canonical result remains heuristic-only and unconstrained. */
        /* The `status' bound is spelled as two inequalities, not as the
           equality the `while' test gives: an `x == <literal>' conjunct on a
           `which implies' LHS makes symexec rewrite `x' to that literal
           inside the LHS's own SPATIAL atoms, and the state carries
           `solver_restart_loop(.., status, solve_wl, M)' with `status' still symbolic, so
           the equality form cannot match.  `lia' recovers `status = 0'. */
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
        /* The semantic call state names only the assumption instance and
           solver model; the two native restart budgets are heuristic. */
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

    if (status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE) {
        /*@ solver_restart_loop(
              s, begin, endvar, n, F, A_arr, status, solve_wl, M) &&
              status <= -2 &&
              -2 <= status
            which implies exists (A_capacity : list literal)
                                 (Mcapacity : msolver),
          ms_cap(Mcapacity) == ms_cap(M) &&
          solver_query_reuse(M, Mcapacity) &&
              assumptions_array(n, begin, endvar, A_arr) *
              solver_prepare_capacity_pre(
                s, n, F, A_arr,
                PropagationStable(A_capacity), Mcapacity, solve_wl) *
              has_permission(&status)
         */
        solver_prepare_public_capacity_exit(s);
        /*@ Assert s == s@pre && begin == begin@pre && endvar == endvar@pre &&
              exists (Mcap : msolver),
              assumptions_array(n, begin, endvar, A_arr) *
              solver_capacity_arm_at(s, n, F, M, Mcap, solve_wl) *
              has_permission(&nof_conflicts) *
              has_permission(&nof_learnts) *
              has_permission(&status) * has_permission(&values) *
              has_permission(&i)
         */
        return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    }

    /*@ solver_restart_loop(
          s, begin, endvar, n, F, A_arr, status, solve_wl, M) &&
          status != 0 &&
          status != -2
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
    /* The two result cases are carried as IMPLICATIONS, not as a top-level
       `||': a disjunctive assertion is a PATH SPLIT in QCP, and splitting
       here would leave `solver_canceluntil' with "Multiple cases inside pre-
       or post-condition".  The split is deferred to the two `if's below,
       where the C control flow provides the paths.  The added interval plus
       `status != 0' is what makes the final fall-through infeasible. */
    /*@ Given Mterminal terminal_levels */
    solver_canceluntil(s, 0);
    if (status == MINISAT_QCP_ONE_VALUE)
        /*@ ms_cap(Mterminal) == ms_cap(M) &&
          solver_terminal_reuse(n, F, A_arr, M, Mterminal, status) &&
          ms_size(Mterminal) == n &&
              status == 1 &&
              (status == 1 =>
                 model_saved(n, F, A_arr, Mterminal) &&
                 solver_sat_cancel_ready(n, F, A_arr, Mterminal)) &&
              solver_cancel_post(s, 0, Mterminal, solve_wl) *
              solver_levels_slice_at(s, Mterminal, terminal_levels)
            which implies exists (Msat : msolver),
          ms_cap(Msat) == ms_cap(M) &&
              solver_sat_arm_at(s, n, F, A_arr, M, Msat, solve_wl) *
              has_permission(&status)
         */
        return 1;
    if (status == -MINISAT_QCP_NEGATIVE_ONE_MAGNITUDE)
        /*@ ms_cap(Mterminal) == ms_cap(M) &&
          solver_terminal_reuse(n, F, A_arr, M, Mterminal, status) &&
          ms_size(Mterminal) == n &&
              status == -1 &&
              (status == -1 =>
                 cnf_unsat(n, cnf_with_units(F, A_arr))) &&
              solver_cancel_post(s, 0, Mterminal, solve_wl) *
              solver_levels_slice_at(s, Mterminal, terminal_levels)
            which implies exists (Munsat : msolver),
          ms_cap(Munsat) == ms_cap(M) &&
              solver_unsat_arm_at(s, n, F, A_arr, M, Munsat, solve_wl) *
              has_permission(&status)
         */
        return 0;
    /* Unreachable: the assertion above pins `status` to exactly 1 or -1 and
       both values are returned by the two preceding branches. */
    /*@ Branch clear all */
    return 0;
}


/* Number of variables the solver currently holds.  Returns the size field and
   leaves it unchanged. */
int solver_nvars(solver* s)
/*@ solver_nvars_spec */
{
    return s->size;
}


/* Read the problem-clause count while preserving its size cell. */
int solver_nclauses(solver* s)
/*@ solver_nclauses_spec */
{
    return vecp_size(&s->clauses);
}


/* Number of conflicts encountered so far, narrowed to an int.  The counter is
   a 64-bit word, so the result is its low 32 bits read as signed. */
int solver_nconflicts(solver* s)
/*@ solver_nconflicts_spec */
{
    return minisat_uint64_to_int(s->stats.conflicts);
}

//=================================================================================================
// Sorting functions (sigh):

/* Selection sort over a pointer array, used for the short segments of the
   learnt-clause sort.  Promises a permutation of the input of the same length;
   the clause objects behind the pointers are never touched. */
static inline void selectionsort(void** array, int size)
/*@ With (db : dbmap) (activities : list fp32) (origin : list Z)
    Require 0 <= size && size <= INT_MAX && Zlength(origin) == size &&
            learnt_sort_context(db, activities) &&
            learnt_sort_segment_domain(db, origin) &&
            PtrArray::seg(array, 0, size, origin) *
            learnt_sort_rep(db, activities)
    Ensure exists (current : list Z),
           Permutation(origin, current) && Zlength(current) == size &&
           PtrArray::seg(array, 0, size, current) *
           learnt_sort_rep(db, activities)
 */
{
    int     i, j, best_i;
    void*   tmp;

    /*@ Inv Assert exists (current : list Z),
                   array == array@pre && size == size@pre &&
                   selectionsort_outer_inv(
                     db, activities, origin, current, size, i) &&
                   Zlength(current) == size &&
                   0 <= i && i <= size &&
                   PtrArray::seg(array, 0, size, current) *
                   learnt_sort_rep(db, activities) *
                   has_permission(&j) * has_permission(&best_i) *
                   has_permission(&tmp)
     */
    for (i = 0; i < size-1; i++){
        best_i = i;
        /*@ Inv Assert exists (current : list Z),
                       array == array@pre && size == size@pre &&
                       selectionsort_inner_inv(
                         db, activities, origin, current,
                         size, i, j, best_i) &&
                       Zlength(current) == size &&
                       0 <= i && i < size - 1 &&
                       i <= best_i && best_i < j &&
                       i + 1 <= j && j <= size &&
                       PtrArray::seg(array, 0, size, current) *
                       learnt_sort_rep(db, activities) *
                       has_permission(&tmp)
         */
        for (j = i+1; j < size; j++){
            if (clause_cmp(array[j], array[best_i]) < 0)
                best_i = j;
        }
        tmp = array[i]; array[i] = array[best_i]; array[best_i] = tmp;
    }
}


/* Randomised quicksort over a pointer array, ordering learnt clauses by
   `clause_cmp` and falling back to selection sort on short segments.  Promises
   a permutation of the input and advances the random seed, whose shadow value
   stays inside the range the contract requires. */
static void sortrnd(void** array, int size, double* seed)
/*@ With (srt_db : dbmap) (srt_activities : list fp32) (srt_origin : list Z)
         seed_value seed_shadow
    Require 0 <= size && size <= INT_MAX && Zlength(srt_origin) == size &&
            learnt_sort_context(srt_db, srt_activities) &&
            learnt_sort_segment_domain(srt_db, srt_origin) &&
            seed_value == Z_to_fp64(seed_shadow) &&
            1 <= seed_shadow && seed_shadow <= 2147483646 &&
            PtrArray::seg(array, 0, size, srt_origin) *
            learnt_sort_rep(srt_db, srt_activities) * store(seed, seed_value)
    Ensure exists (current : list Z) seed_value1 seed_shadow1,
           Permutation(srt_origin, current) && Zlength(current) == size &&
           seed_value1 == Z_to_fp64(seed_shadow1) &&
           1 <= seed_shadow1 && seed_shadow1 <= 2147483646 &&
           PtrArray::seg(array, 0, size, current) *
           learnt_sort_rep(srt_db, srt_activities) * store(seed, seed_value1)
 */
{
    if (size <= 15)
        selectionsort(array, size);

    else{
        void*       pivot = array[irand(seed, size)
                                  /*@ where z = seed_shadow */];
        void*       tmp;
        int         i = -1;
        int         j = size;

        /* PARTITION-SCAN INVARIANT DESIGN (see the two scan invariants below).
           `sortrnd_partition_inv(...,i,j)' carries, besides the permutation
           facts, two STOPPER witnesses:
             L  with  i < L < size,  L <= j,  cmp(current[L], pivot) >= 0
             R  with  0 <= R < j,           cmp(pivot, current[R]) >= 0
           L is what makes the NEXT left scan (which starts at i+1) terminate
           inside the array, R likewise for the next right scan (which starts
           at j-1).  Both bounds are HALF-OPEN AT THE CURSOR because at the
           head of `while (1)' neither cursor has moved yet.  That is correct
           HERE and wrong inside the scans -- see the notes on those two.
           `size <= INT_MAX' is restated because an `Inv Assert' is FULL and
           destroys every pure fact it does not list; without it the four
           `i++'/`j--' overflow safety wits lose their only upper bound on
           `size' and become unprovable. */
        /*@ Inv Assert exists (current : list Z) seed_value_now seed_shadow_now,
                       array == array@pre && size == size@pre &&
                       seed == seed@pre &&
                       sortrnd_partition_inv(srt_db, srt_activities, srt_origin, current,
                                             size, pivot, i, j) &&
                       Zlength(current) == size &&
                       -1 <= i && i < j && 0 < j && j <= size &&
                       size <= INT_MAX &&
                       seed_value_now == Z_to_fp64(seed_shadow_now) &&
                       1 <= seed_shadow_now &&
                       seed_shadow_now <= 2147483646 &&
                       PtrArray::seg(array, 0, size, current) *
                       learnt_sort_rep(srt_db, srt_activities) *
                       store(seed, seed_value_now) *
                       has_permission(&tmp)
         */
        /* symexec SIGSEGVs on a `for' loop that omits its CONDITION -- always --
           or that omits its UPDATE and actually iterates (omitting the init
           alone is safe).  This `while (1)' is the C-standard expansion of the
           original `for(;;)' (C11 6.8.5.3p1), so it is a transcription of the
           frozen upstream loop, not a change of behaviour. */
        while (1) {
            do i++;
            /* LEFT-SCAN INVARIANT.  This cut sits AFTER `i++' and BEFORE the
               test, so `i' is the index about to be compared and the stopper
               may BE `i' itself -- the scan is allowed to stop right here.
               The needed fact is therefore `exists L, i <= L < size', which is
               `sortrnd_partition_inv' AT THE SHIFTED CURSOR `i - 1' (it spells
               its own bound `i-1 < L', i.e. `i <= L').  Passing `i' instead
               would demand `i < L', a STRICTLY stronger fact that the scan
               does not maintain: when the
               stopper is at `i+1' the loop simply exits there, and nothing
               provides a further stopper.  The same off-by-one makes the
               bound `i + 1 < size' false on a reachable state (pivot the last
               element, every earlier element smaller: the scan legitimately
               stops at i = size-1).  `i < size' is the true bound and is what
               the `array[i]' focus needs; `i + 1 < size' is re-derived from the
               shifted L only where the loop actually continues. */
            /*@ Inv Assert exists (current : list Z) seed_value_now
                                 seed_shadow_now,
                           array == array@pre && size == size@pre &&
                           seed == seed@pre &&
                           sortrnd_left_scan_inv(
                             srt_db, srt_activities, srt_origin, current,
                                                 size, pivot, i - 1, j) &&
                           Zlength(current) == size &&
                           0 <= i && i < size && size <= INT_MAX &&
                           0 < j && j <= size &&
                           seed_value_now == Z_to_fp64(seed_shadow_now) &&
                           1 <= seed_shadow_now &&
                           seed_shadow_now <= 2147483646 &&
                           PtrArray::seg(array, 0, size, current) *
                           learnt_sort_rep(srt_db, srt_activities) *
                           store(seed, seed_value_now) *
                           has_permission(&tmp)
             */
            while(clause_cmp(array[i], pivot)<0);
            do j--;
            /* RIGHT-SCAN INVARIANT.  Mirror image of the left scan: the cut is
               AFTER `j--' and BEFORE the test, so the stopper may be `j'
               itself and the needed fact is `exists R, 0 <= R <= j'.
               `sortrnd_right_scan_inv' spells its bound `R < j', so it has to
               be applied AT THE SHIFTED CURSOR `j + 1'.  Passing `j' would
               demand `R < j', which the scan does not maintain: when the only
               stopper is at `j-1' the loop exits there and no earlier stopper
               exists.  For the same reason the bound is `0 <= j' and not
               `0 < j': the scan legitimately stops at j = 0 (pivot at index 0,
               every later element larger).  `0 <= j' is the true bound and is
               what the `array[j]' focus needs. */
            /*@ Inv Assert exists (current : list Z) seed_value_now
                                 seed_shadow_now,
                           array == array@pre && size == size@pre &&
                           seed == seed@pre &&
                           sortrnd_right_scan_inv(
                             srt_db, srt_activities, srt_origin, current,
                                                  size, pivot, i, j + 1) &&
                           Zlength(current) == size &&
                           0 <= i && i < size && size <= INT_MAX &&
                           0 <= j && j < size &&
                           seed_value_now == Z_to_fp64(seed_shadow_now) &&
                           1 <= seed_shadow_now &&
                           seed_shadow_now <= 2147483646 &&
                           PtrArray::seg(array, 0, size, current) *
                           learnt_sort_rep(srt_db, srt_activities) *
                           store(seed, seed_value_now) *
                           has_permission(&tmp)
             */
            while(clause_cmp(pivot, array[j])<0);

            if (i >= j) break;

            tmp = array[i]; array[i] = array[j]; array[j] = tmp;
        }

        /*@ exists (current : list Z) seed_split seed_shadow_split,
              array == array@pre && size == size@pre &&
              seed == seed@pre &&
              Permutation(srt_origin, current) &&
              Zlength(current) == size && 0 <= i && i <= size &&
              learnt_sort_context(srt_db, srt_activities) &&
              learnt_sort_segment_domain(srt_db, current) &&
              seed_split == Z_to_fp64(seed_shadow_split) &&
              1 <= seed_shadow_split &&
              seed_shadow_split <= 2147483646 &&
              PtrArray::seg(array, 0, size, current) *
              learnt_sort_rep(srt_db, srt_activities) *
              store(seed, seed_split) * has_permission(&tmp)
         */
        /*@ Given current seed_split seed_shadow_split */
        /*@ Permutation(srt_origin, current) &&
              Zlength(current) == size && 0 <= i && i <= size &&
              learnt_sort_segment_domain(srt_db, current) &&
              PtrArray::seg(array, 0, size, current)
            which implies exists (left right : list Z),
              sortrnd_split(srt_db, srt_origin, current, left, right, size, i) &&
              PtrArray::seg(array, 0, i, left) *
              PtrArray::seg(array, i, size, right)
         */
        /*@ Given left right */
        sortrnd(array, i, seed)
          /*@ where srt_db = srt_db, srt_activities = srt_activities, srt_origin = left,
                    seed_shadow = seed_shadow_split */;
        /*@ exists (left_after : list Z) seed_after_left shadow_after_left,
              array == array@pre && size == size@pre &&
              seed == seed@pre &&
              Permutation(left, left_after) && Zlength(left_after) == i &&
              seed_after_left == Z_to_fp64(shadow_after_left) &&
              1 <= shadow_after_left &&
              shadow_after_left <= 2147483646 &&
              PtrArray::seg(array, 0, i, left_after) *
              PtrArray::seg(array, i, size, right) *
              learnt_sort_rep(srt_db, srt_activities) *
              store(seed, seed_after_left) * has_permission(&tmp)
         */
        /*@ Given left_after seed_after_left shadow_after_left */
        /* `&array[i]' is program-variable `[]' indexing, which the annotation
           language rejects; the tail base has to be spelled as an explicit
           pointer_offset (same idiom as the reason-array focuses). */
        /*@ PtrArray::seg(array, i, size, right)
            which implies
              PtrArray::seg(
                pointer_offset(array, i, sizeof(void *), void *),
                0, size - i, right)
         */
        sortrnd(&array[i], size-i, seed)
          /*@ where srt_db = srt_db, srt_activities = srt_activities, srt_origin = right,
                    seed_shadow = shadow_after_left */;
        /*@ exists (right_after : list Z) seed_after_right shadow_after_right,
              array == array@pre && size == size@pre &&
              seed == seed@pre &&
              Permutation(right, right_after) &&
              Zlength(right_after) == size - i &&
              seed_after_right == Z_to_fp64(shadow_after_right) &&
              1 <= shadow_after_right &&
              shadow_after_right <= 2147483646 &&
              PtrArray::seg(array, 0, i, left_after) *
              PtrArray::seg(
                pointer_offset(array, i, sizeof(void *), void *),
                0, size - i, right_after) *
              learnt_sort_rep(srt_db, srt_activities) *
              store(seed, seed_after_right) * has_permission(&tmp)
         */
        /*@ Given right_after seed_after_right shadow_after_right */
        /*@ PtrArray::seg(
              pointer_offset(array, i, sizeof(void *), void *),
              0, size - i, right_after)
            which implies PtrArray::seg(array, i, size, right_after)
         */
        /* `i' is carried through on BOTH sides: dropping it from the RHS loses
           its local cell and the block exit then reports
           "Fail to Remove Memory Permission of i". */
        /*@ sortrnd_split(srt_db, srt_origin, current, left, right, size, i) &&
              Permutation(left, left_after) &&
              Permutation(right, right_after) &&
              0 <= i && i <= size &&
              PtrArray::seg(array, 0, i, left_after) *
              PtrArray::seg(array, i, size, right_after)
            which implies exists (joined : list Z),
              joined == app(left_after, right_after) &&
              Permutation(srt_origin, joined) && Zlength(joined) == size &&
              0 <= i && i <= size &&
              PtrArray::seg(array, 0, size, joined)
         */
    }
}

/* Sort a pointer array of learnt clauses worst first.  Opens the clause
   database into the per-clause activities the comparison needs, runs the
   randomised quicksort from a fixed seed, and promises the result is a
   permutation of the input. */
void sort(void** array, int size)
/*@ sort_spec */
{
    /*@ learnt_sort_domain(db, origin) && NoDup(db_words(db)) &&
          clause_db_rep(db)
        which implies exists (activities : list fp32),
          learnt_sort_context(db, activities) &&
          learnt_sort_segment_domain(db, origin) &&
          learnt_sort_rep(db, activities)
     */
    /*@ Given activities */
    double seed = 91648253;
    /* seed_shadow occurs only in pure conjuncts of sortrnd's Require, so it is
       not inferable from the spatial match and must be bound explicitly. */
    sortrnd(array,size,&seed)
      /*@ where srt_db = db, srt_activities = activities, srt_origin = origin,
                seed_shadow = 91648253 */;
    /*@ exists (current : list Z) seed_after,
          Permutation(origin, current) && Zlength(current) == size &&
          learnt_sort_rep(db, activities) *
          PtrArray::seg(array, 0, size, current) *
          store(&seed, seed_after)
        which implies exists (current : list Z),
          Permutation(origin, current) && Zlength(current) == size &&
          PtrArray::seg(array, 0, size, current) * clause_db_rep(db) *
          has_permission(&seed)
     */
}
