#ifndef MINISAT_QCP_COMPAT_H
#define MINISAT_QCP_COMPAT_H

/* MiniSat's verification boundary: its own trusted contracts and Externs. The
   generic runtime layer (vector buffer allocation, resource exhaustion, assert)
   is vec_qcp_runtime.h. In MiniSat's translation units MINISAT_QCP_NATIVE_RUNTIME
   also selects the runtime's native mode; vec_qcp.c does not include this header,
   so a native build passes both flags:
     -DMINISAT_QCP_NATIVE_RUNTIME -DVEC_QCP_NATIVE_RUNTIME
   With only the MiniSat flag the link fails on the undefined vec_* runtime symbols. */
#ifdef MINISAT_QCP_NATIVE_RUNTIME
#ifndef VEC_QCP_NATIVE_RUNTIME
#define VEC_QCP_NATIVE_RUNTIME
#endif
#endif

#include "vec_qcp_runtime.h"
#include "vec_qcp_def.h"

#ifdef MINISAT_QCP_NATIVE_RUNTIME
#include <limits.h>
#ifndef MINISAT_QCP_ENABLE_OUTPUT
#define MINISAT_QCP_ENABLE_OUTPUT
#endif
#endif

struct clause_t;
struct vecp_t;
struct solver_t;

/*@ Extern Coq
      (solver_storage_undef : Z -> Assertion)
      (solver_initial_layout : Z -> Z -> Assertion)
      (MiniSatClause::undef : Z -> bool -> Z -> Assertion)
      (MiniSatClause::owned : Z -> bool -> Z -> Assertion)
      (MiniSatClause::rep : Z -> bool -> list Z -> Assertion)
      (solver_selected_is_learnt : Z -> bool)
      (MiniSatTarget::signed_low32 : Z -> Z)
      (MiniSatTarget::uint64_sum_to_int : Z -> Z -> Z)
      (msat_fp64_value : fp64 -> Prop)
      (DoubleArray::seg : Z -> Z -> Z -> list fp64 -> Assertion)
      (DoubleArray::undef_seg : Z -> Z -> Z -> Assertion)
      (wlists_rep : Z -> Z -> list (list Z) -> Assertion)
 */

double pow(double base, double exponent)
/*@ Require emp
    Ensure msat_fp64_value(__return) && emp
 */;

struct solver_t *minisat_solver_alloc(void)
/*@ Require emp
    Ensure __return != 0 && solver_storage_undef(__return)
 */;

/* Clause allocation assumes even, suitably aligned addresses. The low bit
   distinguishes heap pointers from binary-literal tags. This is an allocator
   assumption, not a consequence of the separation-logic proof; normal return is non-null. The native allocator terminates on failure. */
struct clause_t *minisat_clause_alloc(int size, int learnt)
/*@ Require size > 1 && 0 <= learnt && learnt <= 1 && emp
    Ensure __return != 0 && __return % 2 == 0 && (__return & 1) == 0 &&
           MiniSatClause::undef(__return, solver_selected_is_learnt(learnt), size)
 */;

/* Ownership only, like every free contract here: nothing records that c came
   from minisat_clause_alloc, which libc free requires. */
void minisat_clause_free(struct clause_t *c)
/*@ With size (is_learnt : bool)
    Require MiniSatClause::owned(c, is_learnt, size)
    Ensure emp
 */;

/* MiniSat's batch growth for its per-variable arrays (solver_setnvars), kept here
   because the physical-over-logical capacity design is the solver's.
   Trusted growth contracts retain every initialized element. Physical extents
   can exceed logical capacity after an earlier array succeeds at a larger
   request and a later array falls back. Native realloc tracks its own extent.
   Allocation origin is not represented: p must be NULL or a buffer returned by
   these functions. With no physical extent p must be NULL; solver_array_tail
   carries that fact from solver_new's NULL initialization. */
int *minisat_int_array_grow(int *p, int size, int old_cap, int required, int *new_cap)
/*@ With l physical preferred
    Require 0 <= size && size <= old_cap && old_cap <= physical &&
            physical <= INT_MAX && vec_buf_ok(physical, p) && old_cap < required &&
            required <= preferred && preferred <= INT_MAX &&
            store(new_cap, int, preferred) *
            IntArray::seg(p, 0, size, l) *
            IntArray::undef_seg(p, size, physical)
    Ensure exists actual,
           __return != 0 && required <= actual && actual <= preferred &&
           store(new_cap, int, actual) *
           IntArray::seg(__return, 0, size, l) *
           IntArray::undef_seg(__return, size, actual)
 */;

void **minisat_ptr_array_grow(void **p, int size, int old_cap, int required, int *new_cap)
/*@ With l physical preferred
    Require 0 <= size && size <= old_cap && old_cap <= physical &&
            physical <= INT_MAX && vec_buf_ok(physical, p) && old_cap < required &&
            required <= preferred && preferred <= INT_MAX &&
            store(new_cap, int, preferred) *
            PtrArray::seg(p, 0, size, l) *
            PtrArray::undef_seg(p, size, physical)
    Ensure exists actual,
           __return != 0 && required <= actual && actual <= preferred &&
           store(new_cap, int, actual) *
           PtrArray::seg(__return, 0, size, l) *
           PtrArray::undef_seg(__return, size, actual)
 */;

char *minisat_char_array_grow(char *p, int size, int old_cap, int required, int *new_cap)
/*@ With l physical preferred
    Require 0 <= size && size <= old_cap && old_cap <= physical &&
            physical <= INT_MAX && vec_buf_ok(physical, p) && old_cap < required &&
            required <= preferred && preferred <= INT_MAX &&
            store(new_cap, int, preferred) *
            CharArray::seg(p, 0, size, l) *
            CharArray::undef_seg(p, size, physical)
    Ensure exists actual,
           __return != 0 && required <= actual && actual <= preferred &&
           store(new_cap, int, actual) *
           CharArray::seg(__return, 0, size, l) *
           CharArray::undef_seg(__return, size, actual)
 */;

double *minisat_double_array_grow(double *p, int size, int old_cap, int required, int *new_cap)
/*@ With (l : list fp64) physical preferred
    Require 0 <= size && size <= old_cap && old_cap <= physical &&
            physical <= INT_MAX && vec_buf_ok(physical, p) && old_cap < required &&
            required <= preferred && preferred <= INT_MAX &&
            store(new_cap, int, preferred) *
            DoubleArray::seg(p, 0, size, l) *
            DoubleArray::undef_seg(p, size, physical)
    Ensure exists actual,
           __return != 0 && required <= actual && actual <= preferred &&
           store(new_cap, int, actual) *
           DoubleArray::seg(__return, 0, size, l) *
           DoubleArray::undef_seg(__return, size, actual)
 */;

struct vecp_t *minisat_vecp_array_grow(struct vecp_t *p, int n,
                                       int old_cap, int required, int *new_cap)
/*@ With (wm : list (list Z)) physical preferred
    Require 0 <= n && n <= old_cap && 2 * old_cap <= physical &&
            physical <= INT_MAX && vec_buf_ok(physical, p) && old_cap < required &&
            required <= preferred && 2 * preferred <= INT_MAX &&
            store(new_cap, int, preferred) *
            wlists_rep(p, n, wm) *
            VecpArray::undef_seg(p, 2 * n, physical)
    Ensure exists actual,
           __return != 0 && required <= actual && actual <= preferred &&
           store(new_cap, int, actual) *
           wlists_rep(__return, n, wm) *
           VecpArray::undef_seg(__return, 2 * n, 2 * actual)
 */;

void free(void *ptr);

#ifdef MINISAT_QCP_NATIVE_RUNTIME
#define minisat_solver_alloc() \
    ((struct solver_t *)vec_checked_alloc(1, sizeof(struct solver_t), 0))
#define minisat_clause_alloc(size, learnt) \
    ((struct clause_t *)vec_checked_alloc((size), sizeof(lit), \
        sizeof(struct clause_t) + (learnt) * sizeof(float)))
#define minisat_clause_free(c) free(c)
#define minisat_int_array_grow(p, size, old_cap, required, new_cap) \
    ((int *)vec_checked_grow((p), (required), (new_cap), sizeof(int)))
#define minisat_ptr_array_grow(p, size, old_cap, required, new_cap) \
    ((void **)vec_checked_grow((p), (required), (new_cap), sizeof(void *)))
#define minisat_char_array_grow(p, size, old_cap, required, new_cap) \
    ((char *)vec_checked_grow((p), (required), (new_cap), sizeof(char)))
#define minisat_double_array_grow(p, size, old_cap, required, new_cap) \
    ((double *)vec_checked_grow((p), (required), (new_cap), sizeof(double)))
#define minisat_vecp_array_grow(p, n, old_cap, required, new_cap) \
    ((struct vecp_t *)vec_checked_grow((p), (required), (new_cap), 2 * sizeof(vecp)))
#endif

/* RNG bodies and double-to-int budget casts use trusted external contracts
   on the verification path.
   Heuristic scheduling is outside the SAT/UNSAT certificate. */
#ifndef MINISAT_QCP_NATIVE_RUNTIME
double drand(double* seed)
/*@ With v z
    Require store(seed, v) && v == Z_to_fp64(z) && 1 <= z && z <= 2147483646
    Ensure exists v2 z2, store(seed, v2) && v2 == Z_to_fp64(z2) && 1 <= z2 && z2 <= 2147483646 &&
           fp64_ge(__return, fp64(0.0)) && fp64_lt(__return, fp64(1.0))
*/;

int irand(double* seed, int size)
/*@ With v z
    Require size >= 1 && store(seed, v) && v == Z_to_fp64(z) && 1 <= z && z <= 2147483646
    Ensure exists v2 z2, store(seed, v2) && v2 == Z_to_fp64(z2) && 1 <= z2 && z2 <= 2147483646 &&
           0 <= __return && __return < size
*/;

int minisat_budget_to_int(double x)
/*@ Require emp
    Ensure emp
*/;
#else
#define minisat_budget_to_int(x) \
    ((x) > 2147483647.0 ? 2147483647 : (int)(x))
#endif

#endif /* MINISAT_QCP_COMPAT_H */
