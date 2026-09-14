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

#include "vec_qcp.h"

//=================================================================================================
// Simple types:

// does not work for c++
typedef int  bool;
static const bool  true      = 1;
static const bool  false     = 0;

typedef int                lit;
typedef char               lbool;

#ifdef _WIN32
typedef signed __int64     uint64;   // compatible with MS VS 6.0
#else
typedef unsigned long long uint64;
#endif

static const int   var_Undef = -1;
static const lit   lit_Undef = -2;

static const lbool l_Undef   =  0;
static const lbool l_True    =  1;
static const lbool l_False   = -1;

/* Public contracts and packed-literal functions from the case library. */
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
      (solver_clause_count_cell : Z -> Z -> Assertion)
 */

/* The solve contract is declared once here and named at its definition. */
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
      (msolver_resume_pending : msolver -> msolver)
      (solver_simplify_resumed_pre_at : Z -> Z -> cnf -> list literal -> msolver -> msolver -> Z -> Z -> Assertion)
      (msolver_seed_shadow : msolver -> Prop)
      (solver_query_ready : Z -> cnf -> msolver -> Prop)
      (cnf_nil : cnf)
      (solver_normal_root : Z -> cnf -> msolver -> Prop)
      (solver_rep_growable : Z -> msolver -> Assertion)
      (solver_query_watch_ready : msolver -> Prop)
      (minisat_watch_completed : msolver -> Prop)
      (solver_base_recovery : Z -> cnf -> msolver -> Prop)
      (solver_capacity_exhausted : msolver -> Prop)
      (solver_at_start_or_restart : Z -> cnf -> msolver -> Prop)
 */

static inline lit  toLit   (int v)
/*@ Require 0 <= v && v + v <= INT_MAX && emp
    Ensure __return == v + v && emp
 */
{ return v + v; }
/* lit_neg: pick `bounded` when l is known within an explicit runtime bound
   (0 <= l < 2 * lit_bound_n); `original` when only INT_MAX is known;
   `sentinel` when l may be the lit_Undef sentinel (Require tolerates
   (0 - 2) <= l). */
static inline lit  lit_neg (lit l)
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
 */
{ return l ^ 1; }
/* lit_var: a parallel three-way choice to lit_neg -- `bounded_index` for a
   known runtime bound, `original` when only INT_MAX is known, `zero_index`
   when the caller also holds the assigns array (a different third option
   than lit_neg's `sentinel`: this one needs the assigns array, not sentinel
   tolerance). */
static inline int  lit_var (lit l)
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
            store(pointer_offset(lv_asg, lit_var_c(l), sizeof(char), char),
                  char, Znth(lit_var_c(l), lv_assigns, 0)) *
            CharArray::missing_i(lv_asg, lit_var_c(l), 0,
                                 Zlength(lv_assigns), lv_assigns)
    Ensure __return == lit_var_c(l) &&
           0 <= __return && __return < Zlength(lv_assigns) &&
           Znth(__return, lv_assigns, 0) == 0 &&
           store(pointer_offset(lv_asg, __return, sizeof(char), char),
                 char, Znth(__return, lv_assigns, 0)) *
           CharArray::missing_i(lv_asg, __return, 0,
                                Zlength(lv_assigns), lv_assigns)
 */
/*@ original
    Require 0 <= l && l <= INT_MAX && emp
    Ensure __return == lit_var_c(l) && emp
 */
{ return l >> 1; }
static inline int  lit_sign(lit l)
/*@ Require 0 <= l && l <= INT_MAX && emp
    Ensure __return == lit_sign_c(l) && emp
 */
{ return (l & 1); }


//=================================================================================================
// Public interface:

/* CLIENT PROTOCOL.  Call order: solver_new -> solver_setnvars* (the paper's
   newVar; the PAPER-TO-PORT NAME MAP below says when it is needed) ->
   solver_addclause* -> optionally solver_simplify -> solver_solve*
   (assumptions optional), and then any interleaving of the four after any
   `1` return, after any return of solver_addclause or of solver_setnvars,
   and after a `0` from solver_solve whose returned state is watch-ready
   (dead end 2 below).  After a `-2` from solver_simplify or from
   solver_solve the three calls other than solver_setnvars are contracted.
   Dead end 1 below contracts nothing; dead end 2 contracts nothing on its
   right-hand branch.
   solver_addclause, solver_simplify and solver_solve require the SAME solver
   state -- `solver_update_ready(n, F, nil, M) && solver_query_watch_ready(M)`
   -- and solver_setnvars requires it together with the cleared retry flag,
   `ms_capacity_root_propagation_pending(M) == 0`.  solver_new establishes
   all three; every `1` return, every return of solver_addclause and of
   solver_setnvars, and the watch-ready branch of solver_solve's `0` return
   re-establish all three; the `-2` returns of solver_simplify and of
   solver_solve re-establish the first two only (the flag may be set there).
   A simplify is never mandatory between contracted calls.
   Dead end 1: a `0` from solver_simplify delivers cnf_unsat(n, F); its arm
   carries solver_public_query_entry and solver_query_reuse_guard, not
   solver_query_watch_ready, so the verdict is final and no further call is
   contracted.  Dead end 2: a `0` from solver_solve re-establishes the entry
   state iff the returned state is watch-ready; its arm names exactly that
   alternative, `(solver_query_watch_ready(Mout) || cnf_unsat(n, F))`, and on
   the right-hand branch the clause set itself is unsatisfiable, the verdict
   is final, and no further call is contracted.  Which branch was taken is not
   readable from the return code; the comment block above solver_solve says
   what does discharge it.
   This paragraph is the one normative statement of the protocol: the legend
   below adds only per-code information, and the orientation block of
   solver_qcp.c points here instead of restating it.

   RETURN-CODE LEGEND -- what each code adds BEYOND the state paragraph above,
   for solver_addclause / solver_simplify / solver_solve (solver_setnvars'
   two codes are read off its own Ensure: `1` = the variable count is now
   Z::max(nv, n); `-2` = varmap growth failed, the count is at most n, and
   the solver stays usable with the flag still clear):
   `1`  addclause: the clause was accepted; the stored clause set is only
        MODEL-EQUIVALENT to cnf_add_clause(F, input) (the existential `Fnew`).
        simplify: the solver is query-ready for another contracted call; `1`
        does NOT assert that F is satisfiable or that no root conflict exists
        -- its arm's solver_public_query_entry admits a resident false clause.
        solve: a TOTAL model of F and of every assumption was found, exported
        as ms_model(Mout).
   `0`  addclause: F TOGETHER WITH the rejected clause is unsatisfiable
        (`cnf_unsat(Z::max(n, input_bound), cnf_add_clause(F, input))`), while
        the solver retains F ALONE and stays usable -- a later solve answers
        about F, not about F and the rejected clause.  simplify: cnf_unsat(n,
        F) for the clause set itself.  solve: cnf_unsat(n, cnf_with_units(F,
        A_arr)), i.e. unsatisfiable under the assumptions, plus dead end 2's
        alternative.
   `-2` a fixed-capacity table was exhausted and the solver stays usable.
        simplify and solve report it as solver_capacity_exhausted(Mout);
        addclause's `-2` arm carries no solver_capacity_exhausted fact -- only
        that the solver still holds F, is usable and, like every addclause
        arm, has the pending flag clear.  The C code spells `-2` as
        `-MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE`;
        minisat_qcp_compat.h:30 names the same value
        `MINISAT_CAPACITY_EXHAUSTED`.

   PAPER-TO-PORT NAME MAP: newVar -> solver_setnvars, in batch form, through
   solver_setnvars_incremental_spec below.  That spec composes from every exit
   whose Ensure states solver_query_watch_ready TOGETHER WITH the cleared
   pending flag, which is: solver_new's Ensure, both arms of solver_setnvars
   itself, every arm of solver_addclause, the `1` arm of solver_simplify,
   solver_solve's `1` arm, and solver_solve's `0` arm once
   solver_solve_unsat_arm_usable_after_prior_sat__public discharges that arm's
   alternative (see the solve comment block below).  It does NOT compose from
   solver_simplify's `0` arm or from solve's `0`-with-`cnf_unsat(n, F)` branch
   -- those are final UNSAT verdicts, where a client stops -- nor from the
   `-2` arm of solver_simplify or of solver_solve, which stay usable for
   another solver_addclause / solver_simplify / solver_solve but do not clear
   the pending flag.  addClause -> solver_addclause;
   simplifyDB -> solver_simplify; solve -> solver_solve; model -> the `model`
   vector, surfaced in specs as `ms_model`.  For a NON-EMPTY input
   solver_addclause does grow the solver internally to cover the largest
   variable of that input (its body calls solver_setnvars), but its contract
   does NOT export that fact: the `1` arm promises only `n <= ms_size(Mout)`
   for the ENTRY `n`, and no conjunct there bounds the input's variables by
   `ms_size(Mout)`.  A client that will NAME a new variable in a later call --
   in an assumption array, say, whose `assumptions_array(n, ...)` demands every
   literal below `n` -- therefore calls solver_setnvars for that variable
   first; over variables that already exist the route composes with no growth
   call at all. */

/* GHOST-NAME LEGEND.  Every name in the `Extern Coq` blocks of this header is
   declared with a TYPE only.  This legend gives a one-line reading of each and
   the file it is defined in: lib = Rocq/examples/Applications_human/minisat/
   solver_qcp_lib.v, model = .../solver_qcp_model.v, shared =
   Rocq/cdcllib/sat_shared_lib.v.  The Rocq DEFINITION is authoritative and its
   NAME is the stable key; the line numbers are current at this revision.

   TYPES
     literal   -- `Pos x` / `Neg x`: a variable with a sign (shared:35).
     cnf       -- a list of clauses, a clause being a list of literals
                  (shared:43).
     valuation -- `Z -> bool`, a total assignment (shared:46).
     msolver   -- the ghost solver state: a record holding the logical
                  contents of `struct solver_t` (model:1356).
     mtrail    -- the assigns/levels/trail/trail_lim/qhead core of an msolver
                  (model:305).
     dbmap     -- a clause database: address/clause pairs (model:700).

   GHOST PROJECTIONS (fields of the msolver record, model:1356)
     ms_size(M)  -- number of variables the solver holds, `s->size`
                    (model:1358).
     ms_cap(M)   -- varmap capacity, `s->cap` (model:1359).
     ms_model(M) -- the `model` veci as a list of cells (model:1385).
     ms_prob(M)  -- the problem clause database, `s->clauses` (model:1370);
                    `db_words(ms_prob(M))` is its list of clause words
                    (model:702).
     ms_stats(M) -- the 11-counter statistics vector (model:1403), read only
                    through the named accessors; `stats_conflicts(l)` is
                    `Znth 4 l 0` (model:1317).
     ms_core(M)  -- the mtrail (model:1364).  `mt_lim` is its `trail_lim`
                    list (model:309), so `Zlength(mt_lim(ms_core(M))) == 0`
                    says "at decision level 0".
     ms_root_level(M) -- `s->root_level` (model:1365).
     ms_capacity_root_propagation_pending(M) -- the public retry flag
                    (model:1362): 1 exactly when a root propagation was
                    suspended by a `-2` exit, 0 otherwise.

   SOLVER-STATE PREDICATES (the incremental vocabulary a client composes in)
     solver_update_ready(n, F, A, M) -- after restoring any suspended
       propagation, M satisfies the strong assuming invariant for n variables
       and clause set F, sits at decision level 0, and has the retry flag
       clear (lib:42850).
     solver_query_watch_ready(M) -- the watcher table is complete: of M when
       the retry flag is 0, of the resumed M when it is 1 (lib:9852;
       minisat_watch_completed lib:9112).
     solver_incremental_ownership_at(s, M) -- ownership of the whole struct
       `s` at M, plus the RNG seed shadow and `2 * ms_cap(M) <= INT_MAX`;
       unfolding it yields solver_rep_growable (lib:42130).
     solver_rep_growable(s, M) -- whole-struct footprint with the watcher
       growth slack framed (lib:34903).  solver_rep_wl(s, M, wl) is the same
       footprint with the watcher base address `wl` named (lib:5934).
     solver_public_query_entry(n, F, M) -- M may start a query: query-ready,
       or a suspended root, or a base state with a resident false clause
       (lib:9866) -- it does NOT exclude a root conflict.
     solver_query_reuse_guard(M) -- watch-ready, or retry flag clear together
       with a resident false clause (lib:9874); implied by
       solver_query_watch_ready.
     solver_query_reentry(n, F, M) -- query-ready with a complete watcher
       table, or a base state with a resident false clause (lib:9870).
     solver_query_ready(n, F, M) -- strong assuming invariant, decision level
       0, drained root queue, retry flag clear (lib:9845).
     solver_base_recovery(n, F, M) -- a base state plus a complete watcher
       table or a resident false clause (lib:9858).
     solver_normal_root(n, F, M) -- root level 0, drained root queue, retry
       flag clear (lib:9803).
     solver_at_start_or_restart(n, F, M) -- an operational root: normal or
       suspended (lib:10031).
     solver_capacity_exhausted(M) -- the learnt vector or some watcher list
       reached its fixed capacity (model:3120).
     msolver_seed_shadow(M) -- the RNG seed is exactly an integer in the
       permitted range (model:2599).
     msolver_resume_pending(M) -- M with a suspended root propagation
       restored; M itself when the flag is 0 (lib:9879).
     solver_shape(M) -- the size/capacity well-formedness of M (model:1709).
     solver_support_inv(n, F, A, I, root, M) -- the solver invariant of M with
       its stored assumption root replaced by `root` (lib:9831).
     solver_clause_count_cell(s, n) -- the size cell of the `clauses` vector
       alone, owning nothing else (lib:5910).
     solver_simplify_post_at, solver_simplify_resumed_pre_at,
     addclause_support_post_at -- the folded post/preconditions of the general
       specs (lib:10272, lib:10115, lib:40632); the comment blocks above those
       specs say what they contain.

   FORMULA, MODEL AND INPUT VOCABULARY
     cnf_nil -- the empty clause set (lib:42617).
     cnf_add_clause(F, input) -- F with the packed literal list `input`
       appended as one clause (lib:42925).
     cnf_with_units(F, A) -- F with one unit clause per assumption
       (shared:1418).
     cnf_unsat(n, F) -- F is well formed over n variables and NO valuation
       bounded by n models it (shared:148).
     models(rho, F) -- rho satisfies every clause of F (shared:134).
     rho_of_model(l) -- reads cell x of l as TRUE iff that cell is 1
       (lib:7871).
     model_is_total(l) -- every cell of l is 1 or -1 (lib:7970).
     assumptions_true_under(rho, A) -- every assumption literal is true under
       rho (lib:7976).
     assumptions_array(n, begin, endvar, A) -- a caller-owned `lit[]` over
       [begin, endvar) whose packed literals denote A and each satisfy
       lit_wf_c(n); when the list is EMPTY, `begin` must still be a valid int
       address -- in range and sizeof(int)-aligned, which NULL satisfies
       (lib:9793, valid_int_position lib:9787).
     lit_wf_c(n, l) -- `0 <= l < 2 * n`: l is a packed literal of a variable
       below n (model:83).
     lit_neg_c(l), lit_var_c(l), lit_sign_c(l) -- the packed-literal
       functions `l ^ 1`, `l / 2`, `l & 1` (model:85, model:87, lib:142).
     Forall and Z::max are Rocq's own; MiniSatTarget::signed_low32 is declared
       in minisat_qcp_compat.h:21 and defined at lib:102. */


/* Public incremental predicates; implementations keep their general specs.
   `ms_capacity_root_propagation_pending(M)` is public vocabulary because the
   incremental contracts promise it and solver_setnvars_incremental_spec
   requires it: 1 = a root propagation was suspended by a `-2` exit; 0
   otherwise.  `ms_prob`/`db_words`, `ms_stats` and `stats_conflicts` are
   public only as the values the three accessors' incremental specs return;
   `Zlength(db_words(ms_prob(M)))` is the resident problem-database length,
   equivalently `Zlength(ms_prob(M))` -- see WHAT THE COUNT IS below. */
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

/* Names used only by the general, body-proved specs below.  All three
   general specs (addclause, simplify, solve) are declared on this header
   beside their incremental counterparts, and setnvars' exit state is spelled
   out rather than folded, which is why these appear here at all.  They are
   internal notions; a client composes against the `*_incremental_spec`
   contracts -- including solver_setnvars_incremental_spec -- which need none
   of them.  `ms_capacity_root_propagation_pending` is NOT in this block: it
   is public vocabulary, declared above and glossed in the GHOST-NAME LEGEND.
   A proof that does need the internal names from the public ones unfolds
   solver_update_ready itself (see the GHOST-NAME LEGEND): its body is the
   strong assuming invariant at decision level 0 with the retry flag clear,
   all stated of msolver_resume_pending(M).  The spec-derivation proofs in
   solver_qcp_proof_manual_part9.v --
   `proof_of_solver_addclause_derive_solver_addclause_incremental_spec_by_addclause_spec`
   and its siblings -- make that conversion once; a client composing the
   incremental specs never has to. */
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

/* Allocation uses the same success-assumed typed allocator boundary as
   veci_new/vecp_new. The checked body produces this state from raw storage.

   The exit state is spelled in exactly the names the next call requires:
   `solver_update_ready(0, cnf_nil, nil, M) && solver_query_watch_ready(M)
   && solver_incremental_ownership_at(__return, M)` IS, verbatim, the
   solver-state part of the Require of solver_addclause_incremental_spec,
   solver_simplify_incremental_spec and solver_solve_incremental_spec below --
   and the WHOLE Require of solver_simplify_incremental_spec.  With
   `ms_capacity_root_propagation_pending(M) == 0` beside them it is also the
   whole solver-state part of solver_setnvars_incremental_spec's Require, so
   the paper's first step, solver_new -> newVar, composes by text.  The other
   two add only conjuncts about the caller's own input buffer (addclause: the
   `IntArray::seg` holding the clause, its `input_bound` range, its length
   arithmetic and `Forall(lit_wf_c(input_bound), input)`; solve:
   `assumptions_array`), so a client composes solver_new with any of the three
   by matching the solver-state text and then supplying its own buffer.  (`solver_incremental_ownership_at` also carries
   `msolver_seed_shadow(M)` and `2 * ms_cap(M) <= INT_MAX`; unfolding it
   yields the `solver_rep_growable(__return, M)` the general specs take.)
   `solver_normal_root(0, cnf_nil, M)` is kept as well and is strictly
   stronger THAN THE `solver_update_ready(0, cnf_nil, nil, M)` CONJUNCT BESIDE
   IT -- it adds a drained root queue, and it also names root level 0 and the
   cleared retry flag, which this Ensure states on its own as well.  It does
   not subsume `solver_query_watch_ready(M)`, which is a separate conjunct of
   this Ensure.  It is an internal name (solver_qcp_def.h), retained only
   because the general specs of solver_setnvars and solver_addclause are
   stated in terms it supplies and dropping it would narrow this contract; a
   client composing the incremental specs never needs it. */
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
/* Native-only: the body sits inside the `#ifdef MINISAT_QCP_NATIVE_RUNTIME`
   guard around `solver_delete` in solver_qcp.c (c:11173).  Not part of the
   verified configuration and carries no contract -- see the sentence
   "Deletion, parser/I/O and optional configurations remain outside this
   scope" in the orientation block of solver_qcp.c (c:46). */
extern void    solver_delete(solver* s);

/* Spec derivation (applies to every `<=` below): the right-hand name is the
   general, body-proved specification; the left-hand incremental spec is a
   proved consequence of it (a Qed lemma in the manual proof lane) and is the
   one a client composes against.

   A `1` return's existential Fnew is only model-equivalent to
   cnf_add_clause(F, input): the stored clause set may be a simplification of
   F && C, not F && C itself.  The returned array (`current`) has fresh,
   unconstrained contents on every return: the caller's literal array is
   destroyed by this call.  A `0` return still promises solver_update_ready
   and solver_query_watch_ready, i.e. the solver remains usable -- a stronger
   guarantee than treating the post-`0` state as unusable.

   The general spec (addclause_spec, at its definition site) threads an
   assumption list (ac_A_arr/ac_A_inst) for the body's internal reuse of the
   propagation lemmas; this public (incremental) spec fixes it to nil. */
extern int     solver_addclause(solver* s, lit* begin, lit* endvar)
/*@ addclause_spec
    With (ac_F : cnf) (ac_A_arr ac_A_inst : list literal) (ac_M ac_physical_entry : msolver)
         (ac_n : Z) (ac_input : list Z)
    Require ac_M == msolver_resume_pending(ac_physical_entry) &&
            0 <= ac_n && ac_n <= Z::max(ms_cap(ac_M), INT_MAX / 4) &&
            2 * ms_cap(ac_M) <= INT_MAX &&
            endvar == begin + Zlength(ac_input) * sizeof(int) &&
            2 * Zlength(ac_input) + 1 <= INT_MAX &&
            Forall(lit_wf_c(ac_n), ac_input) &&
            solver_shape(ac_M) &&
          solver_support_inv(ms_size(ac_M), ac_F, ac_A_arr, ac_A_inst, 0, ac_M) &&
            ms_capacity_root_propagation_pending(ac_M) == 0 &&
            Zlength(mt_lim(ms_core(ac_M))) == 0 &&
            msolver_seed_shadow(ac_M) &&
            solver_rep_growable(s, ac_physical_entry) *
            IntArray::seg(begin, 0, Zlength(ac_input), ac_input)
    Ensure addclause_support_post_at(s, begin, ac_n, ac_F, ac_A_arr,
                             ac_A_inst, ac_M, ac_input, __return)
 */
/*@ solver_addclause_incremental_spec <= addclause_spec
    With (n input_bound : Z) (F : cnf) (M : msolver) (input : list Z)
    Require solver_update_ready(n, F, nil, M) &&
            solver_query_watch_ready(M) &&
            0 <= input_bound && input_bound <= Z::max(ms_cap(M), INT_MAX / 4) &&
            endvar == begin + Zlength(input) * sizeof(int) &&
            2 * Zlength(input) + 1 <= INT_MAX &&
            Forall(lit_wf_c(input_bound), input) &&
            solver_incremental_ownership_at(s, M) *
            IntArray::seg(begin, 0, Zlength(input), input)
    Ensure exists (Mout : msolver) (current : list Z),
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
        solver_update_ready(ms_size(Mout), F, nil, Mout)) ||
       (__return == -2 &&
        solver_update_ready(ms_size(Mout), F, nil, Mout))) &&
      solver_incremental_ownership_at(s, Mout) *
      IntArray::seg(begin, 0, Zlength(input), current)
 */;
/* solver_simplify_spec threads an assumption list (smp_A_arr) for the
   body's internal reuse of propagation lemmas; the public (incremental)
   spec below fixes it to nil.

   The return code and its promise are not visible in this Ensure, and cannot
   be made visible here: a top-level `||` or a `__return`-conditional in a
   callee postcondition is a PATH SPLIT at symbolic-execution time, and
   solver_search calls solver_simplify against this very spec (solver_qcp.c,
   the `which implies` blocks after that call rely on the folded predicate --
   see the note there).  Measured when the fold was introduced: the
   disjunctive form aborts symexec ("Sep cannot be fully solved"), and the
   split-free conditional form re-emits a large part of solver_search's
   verification conditions -- of which there are 1283 (`grep -c "^Definition
   solver_search_" solver_qcp_goal.v`).  The exact re-emission count is not
   reproducible from this tree and is not claimed here.

   The folded `solver_simplify_post_at(s, ..., __return, ...)` is exactly a
   three-way disjunction over its three named arms,
   solver_simplify_post_{sat,unsat,retry}_at, proved equal to it (bi-entailment)
   by solver_simplify_post_at_arms__api_reentry (solver_qcp_lib.v:10401, Qed);
   the arm Definitions (lib.v:10350, 10367, 10383) are authoritative and a
   gloss of every conjunct each one carries sits beside them there.  The
   client-facing CONSEQUENCE of those arms -- deliberately weaker, not the
   same arms written out -- is solver_simplify_incremental_spec below, proved
   from the general spec by
   `proof_of_solver_simplify_derive_solver_simplify_incremental_spec_by_solver_simplify_spec`
   (solver_qcp_proof_manual_part9.v:1945, Qed). */
extern int     solver_simplify(solver* s)
/*@ solver_simplify_spec
    With (smp_n : Z) (smp_F : cnf) (smp_A_arr : list literal)
         (M smp_physical_entry : msolver) (levels_ptr smp_wl : Z)
    Require solver_simplify_resumed_pre_at(
              s, smp_n, smp_F, smp_A_arr, smp_physical_entry, M, levels_ptr, smp_wl)
    Ensure solver_simplify_post_at(
             s, smp_n, smp_F, smp_A_arr, M, levels_ptr, __return, smp_wl)
 */
/*@ solver_simplify_incremental_spec <= solver_simplify_spec
    With (n : Z) (F : cnf) (M : msolver)
    Require solver_update_ready(n, F, nil, M) &&
            solver_query_watch_ready(M) &&
            solver_incremental_ownership_at(s, M)
    Ensure exists (Mout : msolver),
      solver_update_ready(n, F, nil, Mout) &&
      ((__return == 1 &&
        solver_public_query_entry(n, F, Mout) &&
        solver_query_reuse_guard(Mout) &&
        ms_capacity_root_propagation_pending(Mout) == 0 &&
        solver_query_watch_ready(Mout)) ||
       (__return == 0 &&
        cnf_unsat(n, F) &&
        solver_public_query_entry(n, F, Mout) &&
        ms_capacity_root_propagation_pending(Mout) == 0 &&
        solver_query_reuse_guard(Mout)) ||
       (__return == -2 &&
        solver_capacity_exhausted(Mout) &&
        solver_query_watch_ready(Mout))) &&
      solver_incremental_ownership_at(s, Mout)
 */;
/* solver_solve_spec (the general spec) conditions three postconditions on
   solver_query_reuse_guard(M).  Its Require demands solver_query_watch_ready(M),
   and that IMPLIES the guard (the guard is watch-readiness OR a cleared
   pending flag together with a resident false clause), so for every
   contracted call the three guarded conjuncts hold unconditionally.  The
   guard is kept in the Ensure text only so that the existing proofs and the
   derived incremental spec keep their shape; it costs a caller nothing.
   In particular the solver_base_recovery and solver_query_reentry of the
   `__return == 0` arm of solver_solve_spec always apply, and supply the entry
   state for another call with no intervening simplify -- whenever that state
   is watch-ready.  The incremental spec below turns that into one named
   alternative on its own `__return == 0` arm,
   `(solver_query_watch_ready(Mout) || cnf_unsat(n, F))`, beside the cleared
   pending flag that the `1` and `0` arms also state.  A client that reaches the second
   branch has a final UNSAT verdict for F and stops.  The alternative is not
   observable from the return code -- both branches return `0` -- but it IS
   discharged by call history: a client whose last solve on the SAME `F`
   returned `1`, with no solver_addclause in between (an addclause `1`
   rebinds `F` to a fresh existential `Fnew`), holds
   `models(rho_of_model(ms_model(..)), F)`, which refutes `cnf_unsat(n, F)`
   and leaves the left disjunct; the entailment is
   `solver_solve_unsat_arm_usable_after_prior_sat__public`
   (solver_qcp_lib.v, Qed).  Distinguishing the two branches by a separate
   return code would change the executable and is deliberately not done
   here.

   The general spec exposes the watcher-table base address `solve_wl` as a
   public `With`-binder because the body's assertions name it directly; the
   incremental spec below hides it inside solver_incremental_ownership_at.

   THE MODEL.  ms_model(Msat) is the logical view of the C `model` vector.  On
   the `1` arm its length is `n` (`Zlength(ms_model(Mout)) == n`) and every
   cell is 1 or -1 (`model_is_total`, solver_qcp_lib.v:7970); `rho_of_model`
   (solver_qcp_lib.v:7871) reads cell x as TRUE iff it is 1, so 1 = true,
   -1 = false, and 0 never occurs.  The memory tie is peel_vecs_model
   (solver_qcp_lib.v:6393, Qed), reached by unfolding
   solver_incremental_ownership_at (lib.v:42130) -> solver_rep_growable
   (lib.v:34903) -> solver_rep_at (solver_qcp_model.v:2243) ->
   solver_nonlevel_rep_at (model.v:1842) -> solver_nonlevel_rep_nostats_at
   (model.v:1812) -> solver_vecs_rep (model.v:1770); there is no public
   accessor for a single model cell.

   THE ASSUMPTION BUFFER.  `assumptions_array(n, begin, endvar, A_arr)`
   (solver_qcp_lib.v:9793) is a caller-owned `lit[]` over [begin, endvar)
   whose packed literals denote A_arr and each satisfy `lit_wf_c(n)`, i.e.
   `0 <= l < 2 * n`; when the list is EMPTY it still requires
   `valid_int_position begin` (lib.v:9787: in range and
   sizeof(int)-aligned), which NULL satisfies but an arbitrary junk pointer
   does not. */
extern int     solver_solve(solver* s, lit* begin, lit* endvar)
/*@ solver_solve_spec
    With (solve_wl : Z) (n : Z) (F : cnf) (A_arr : list literal) (M : msolver)
    Require solver_update_ready(n, F, nil, M) &&
            solver_query_watch_ready(M) &&
            msolver_seed_shadow(M) &&
            solver_rep_wl(s, M, solve_wl) *
            assumptions_array(n, begin, endvar, A_arr)
    Ensure assumptions_array(n, begin, endvar, A_arr) *
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
                solver_rep_wl(s, Munsat, solve_wl))) ||
            (__return == -2 &&
             (exists (Mretry : msolver),
                ms_size(Mretry) == n &&
                solver_capacity_exhausted(Mretry) &&
                solver_at_start_or_restart(n, F, Mretry) &&
                msolver_seed_shadow(Mretry) &&
                ms_cap(Mretry) == ms_cap(M) &&
                (solver_query_reuse_guard(M) => solver_query_watch_ready(Mretry)) &&
                solver_rep_wl(s, Mretry, solve_wl))))
 */
/*@ solver_solve_incremental_spec <= solver_solve_spec
    With (n : Z) (F : cnf) (A_arr : list literal) (M : msolver)
    Require solver_update_ready(n, F, nil, M) &&
            solver_query_watch_ready(M) &&
            solver_incremental_ownership_at(s, M) *
            assumptions_array(n, begin, endvar, A_arr)
    Ensure assumptions_array(n, begin, endvar, A_arr) *
      (exists (Mout : msolver),
        solver_public_query_entry(n, F, Mout) &&
        solver_query_reuse_guard(Mout) &&
        solver_update_ready(n, F, nil, Mout) &&
        ((__return == 1 &&
          Zlength(ms_model(Mout)) == n &&
          model_is_total(ms_model(Mout)) &&
          models(rho_of_model(ms_model(Mout)), F) &&
          assumptions_true_under(rho_of_model(ms_model(Mout)), A_arr) &&
          ms_capacity_root_propagation_pending(Mout) == 0 &&
          solver_query_watch_ready(Mout)) ||
         (__return == 0 &&
          cnf_unsat(n, cnf_with_units(F, A_arr)) &&
          ms_capacity_root_propagation_pending(Mout) == 0 &&
          (solver_query_watch_ready(Mout) || cnf_unsat(n, F))) ||
         (__return == -2 &&
          solver_capacity_exhausted(Mout) &&
          solver_at_start_or_restart(n, F, Mout) &&
          solver_query_watch_ready(Mout))) &&
        solver_incremental_ownership_at(s, Mout))
 */;

/* solver_nvars and solver_nconflicts are declared WITH their contracts at the
   end of this header, below `struct solver_t`: their Requires name struct
   fields (`s->size`, `s->stats.conflicts`), which needs the layout in scope.

   All three accessors also carry an `*_incremental_spec <= *_spec` whose
   Require is the route's own `solver_incremental_ownership_at(s, M)`, so a
   client never has to open the ownership fold to read a counter -- and can
   at last learn `ms_size(M)`, the `n` every later Require is indexed by.
   The raw-cell specs are kept for the body proofs that call them.
   What each one returns, in the incremental vocabulary:
   solver_nvars_incremental_spec -- `ms_size(M)`, the variable count the next
   Require is indexed by; solver_nclauses_incremental_spec --
   `Zlength(db_words(ms_prob(M)))`, the resident problem-database length, NOT
   `Zlength(F)` (see WHAT THE COUNT IS below);
   solver_nconflicts_incremental_spec --
   `MiniSatTarget::signed_low32(stats_conflicts(ms_stats(M)))`, the conflict
   counter narrowed to an int.  Each also returns the ownership it took, so
   the route continues unchanged across an accessor call. */

/* WHAT THE COUNT IS.  solver_nclauses returns the size cell of the solver's
   `clauses` vector, and the Ensure below says only that -- it relates
   `__return` to the abstract cell `solver_clause_count_cell(s, n)` and to
   nothing else, because this read-only query does not take the
   `solver_rep_growable(s, M)` that would connect it to a model state.

   For a solver that does represent the model state `M`, that cell holds
   `Zlength(db_words(ms_prob(M)))`, equivalently `Zlength(ms_prob(M))`: the
   number of clauses RESIDENT IN THE PROBLEM DATABASE.  It is deliberately NOT
   `Zlength(F)` for the clause set `F` the client inserted.  The stored
   database is only MODEL-EQUIVALENT to `F`: solver_addclause may skip a
   tautology, drop literals that are false at the root, or store a shortened
   clause, none of which changes which valuations satisfy the set but any of
   which changes the count.  A caller must therefore read this as an
   implementation observation about the database, never as a property of `F`.

   Two lemmas in solver_qcp_lib.v state exactly this and are what a proof
   about the count should use:
     solver_clause_count_cell_problem_clauses__api_reentry -- the `clauses`
       vector of a solver holding `db_words(ms_prob(M))` yields
       `solver_clause_count_cell(s, Zlength(db_words(ms_prob(M))))`;
     solver_problem_clause_count_length__api_reentry --
       `Zlength(db_words(ms_prob(M))) = Zlength(ms_prob(M))`. */
extern int     solver_nclauses(solver* s)
/*@ solver_nclauses_spec
    With n
    Require solver_clause_count_cell(s, n)
    Ensure __return == n && solver_clause_count_cell(s, n)
 */
/*@ solver_nclauses_incremental_spec <= solver_nclauses_spec
    With (M : msolver)
    Require solver_incremental_ownership_at(s, M)
    Ensure __return == Zlength(db_words(ms_prob(M))) &&
           solver_incremental_ownership_at(s, M)
 */;

/* Grow the solver to hold at least `n` variables.  `1` on success, `-2` when a
   growth step cannot allocate, leaving a consistent solver at whatever size it
   had reached.  The postcondition is spelled out rather than folded into a
   single named predicate: the 1/-2 split and the resulting size are what a
   caller reads off it.  `ms_size(Mnew) == Z::max(ms_size(sn_M), n)` on the `1`
   arm is the reader's phrasing of the folded predicate `setnvars_post_at`
   (solver_qcp_lib.v:35106), whose text is
   `n <= ms_size(Mnew) && (ms_size(Mnew) == n || ms_size(Mnew) == ms_size(sn_M))`;
   the two are equivalent under `ms_size(sn_M) <= ms_size(Mnew)`, also promised
   here.  Growth PRESERVES, but does not establish, a drained root queue, a
   cleared pending flag, the RNG seed shadow and watcher completeness: those
   are promised only as consequences of the same facts holding at entry.

   solver_setnvars_incremental_spec below is the client-facing consequence of
   setnvars_spec, written in the SAME vocabulary as the other three
   incremental specs, so the paper's `newVar` step composes without reading
   solver_qcp_lib.v.  Beyond the usual three it requires
   `ms_capacity_root_propagation_pending(M) == 0` -- a suspended root
   propagation is exactly what setnvars_spec's conditional postcondition
   cannot restore -- and the range `0 <= n && n <= Z::max(ms_cap(M), INT_MAX /
   4)`, which a client discharges without knowing `ms_cap(M)` by keeping
   `n <= INT_MAX / 4` (`Z.le_max_r`).  solver_new, both arms of this spec,
   every arm of solver_addclause, and the `1` and `0` arms of solver_simplify
   and of solver_solve promise the flag conjunct; the `-2` arms of
   solver_simplify and of solver_solve do not: solve's `-2` is the one exit
   that can leave the flag set (a root propagation suspended by the capacity
   exit), and simplify's `-2` arm, though the executable leaves the flag clear
   on that path, does not promise it -- so a client that reaches either cannot
   call solver_setnvars against this spec.  Watch-readiness is a SECOND Require
   conjunct, and it is
   what rules out two more exits: simplify's `0` arm promises the flag but
   only solver_query_reuse_guard, and solve's `0` arm promises watch-readiness
   only as the left disjunct of an alternative.  The exits this spec composes
   from are therefore exactly the ones listed in the PAPER-TO-PORT NAME MAP at
   the top of this header. */
extern int     solver_setnvars(solver* s, int n)
/*@ setnvars_spec
    With (sn_F : cnf) (sn_A_arr sn_A_inst : list literal) (sn_M : msolver) sn_root
    Require 0 <= n && n <= Z::max(ms_cap(sn_M), INT_MAX / 4) &&
            2 * ms_cap(sn_M) <= INT_MAX &&
          solver_support_inv(ms_size(sn_M), sn_F, sn_A_arr, sn_A_inst, sn_root, sn_M) &&
            solver_rep_growable(s, sn_M)
    Ensure exists (Mnew : msolver),
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
      ((__return == 1 && ms_size(Mnew) == Z::max(ms_size(sn_M), n)) ||
       (__return == -2 && ms_size(Mnew) <= n)) &&
      solver_rep_growable(s, Mnew)
 */
/*@ solver_setnvars_incremental_spec <= setnvars_spec
    With (nv : Z) (F : cnf) (M : msolver)
    Require solver_update_ready(nv, F, nil, M) &&
            solver_query_watch_ready(M) &&
            ms_capacity_root_propagation_pending(M) == 0 &&
            0 <= n && n <= Z::max(ms_cap(M), INT_MAX / 4) &&
            solver_incremental_ownership_at(s, M)
    Ensure exists (Mnew : msolver),
      nv <= ms_size(Mnew) &&
      solver_update_ready(ms_size(Mnew), F, nil, Mnew) &&
      solver_query_watch_ready(Mnew) &&
      ms_capacity_root_propagation_pending(Mnew) == 0 &&
      ((__return == 1 && ms_size(Mnew) == Z::max(nv, n)) ||
       (__return == -2 && ms_size(Mnew) <= n)) &&
      solver_incremental_ownership_at(s, Mnew)
 */;

struct stats_t
{
    uint64   starts;
    uint64   decisions;
    uint64   propagations;
    uint64   inspects;
    uint64   conflicts;
    uint64   clauses;
    uint64   clauses_literals;
    uint64   learnts;
    uint64   learnts_literals;
    uint64   max_literals;
    uint64   tot_literals;
};
typedef struct stats_t stats;

//=================================================================================================
// Solver representation:

struct clause_t;
typedef struct clause_t clause;

struct solver_t
{
    int      size;          // nof variables
    int      cap;           // size of varmaps
    int      qhead;         // Head index of queue.
    int      qtail;         // Tail index of queue.
    int      capacity_pending_qhead; // Saved root propagation cursor across public -2.
    int      capacity_root_propagation_pending;

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

//=================================================================================================
// Public accessors whose contracts name struct fields:

/* Number of variables the solver currently holds; the size field, unchanged. */
extern int     solver_nvars(solver* s)
/*@ solver_nvars_spec
    With n
    Require store(&(s->size), n)
    Ensure __return == n && store(&(s->size), n)
 */
/*@ solver_nvars_incremental_spec <= solver_nvars_spec
    With (M : msolver)
    Require solver_incremental_ownership_at(s, M)
    Ensure __return == ms_size(M) && solver_incremental_ownership_at(s, M)
 */;
/* Number of conflicts encountered so far, narrowed to an int.  The counter is
   a 64-bit word, so the result is its low 32 bits read as signed;
   MiniSatTarget::signed_low32 (minisat_qcp_compat.h:21) names that narrowing. */
extern int     solver_nconflicts(solver* s)
/*@ solver_nconflicts_spec
    With conflicts
    Require store(&(s->stats.conflicts), conflicts)
    Ensure __return == MiniSatTarget::signed_low32(conflicts) &&
           store(&(s->stats.conflicts), conflicts)
 */
/*@ solver_nconflicts_incremental_spec <= solver_nconflicts_spec
    With (M : msolver)
    Require solver_incremental_ownership_at(s, M)
    Ensure __return == MiniSatTarget::signed_low32(stats_conflicts(ms_stats(M))) &&
           solver_incremental_ownership_at(s, M)
 */;
