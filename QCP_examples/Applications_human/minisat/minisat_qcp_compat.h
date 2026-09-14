#include "verification_stdlib.h"

#define NULL 0

struct clause_t;
struct vecp_t;
struct solver_t;

#ifdef MINISAT_QCP_ENABLE_OUTPUT
int printf();
int fflush();
extern void *stdout;
#endif

/*@ Extern Coq
      (solver_storage_undef : Z -> Assertion)
      (solver_initial_layout : Z -> Z -> Assertion)
      (MiniSatClause::undef : Z -> Z -> Assertion)
      (MiniSatClause::owned : Z -> Z -> Assertion)
      (MiniSatClause::rep : Z -> bool -> list Z -> Assertion)
      (MiniSatTarget::signed_low32 : Z -> Z)
      (MiniSatTarget::uint64_sum_to_int : Z -> Z -> Z)
      (msat_fp64_value : fp64 -> Prop)
      (DoubleArray::seg : Z -> Z -> Z -> list fp64 -> Assertion)
      (DoubleArray::undef_seg : Z -> Z -> Z -> Assertion)
      (wlists_rep : Z -> Z -> list (list Z) -> list Z -> Assertion)
      (wlists_undef : Z -> Z -> Z -> Assertion)
 */

#define MINISAT_CAPACITY_EXHAUSTED (-2)
#define MINISAT_MAX_GROWABLE_CAP 1073741823

/* QCP rejects object-like macro expansions whose folded value is negative.
   Keep native public constants unchanged; negate positive magnitudes at use sites. */
#define MINISAT_QCP_ZERO_VALUE 0
#define MINISAT_QCP_ONE_VALUE 1
#define MINISAT_QCP_NEGATIVE_ONE_MAGNITUDE 1
#define MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE 2

double pow(double base, double exponent)
/*@ Require emp
    Ensure msat_fp64_value(__return) && emp
 */;

/* Raw solver allocation follows the existing successful-allocation boundary.
   Its footprint contains only undefined C fields, no solver invariant. */
struct solver_t *minisat_solver_alloc(void)
/*@ Require emp
    Ensure __return != 0 && solver_storage_undef(__return)
 */;

int *minisat_int_array_alloc(int cap)
/*@ Require cap > 0 && emp
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
 */;

int *minisat_int_array_realloc(int *p, int old_cap, int new_cap)
/*@ With size l
    Require 0 <= size && size == old_cap && old_cap < new_cap &&
            IntArray::seg(p, 0, size, l)
    Ensure __return != 0 &&
           IntArray::seg(__return, 0, size, l) *
           IntArray::undef_seg(__return, size, new_cap)
 */;

void minisat_int_array_free(int *p)
/*@ With size cap l
    Require 0 <= size && size <= cap &&
            IntArray::seg(p, 0, size, l) *
            IntArray::undef_seg(p, size, cap)
    Ensure emp
 */;

void **minisat_ptr_array_alloc(int cap)
/*@ Require cap > 0 && emp
    Ensure __return != 0 && PtrArray::undef_full(__return, cap)
 */;

void **minisat_ptr_array_realloc(void **p, int old_cap, int new_cap)
/*@ With size l
    Require 0 <= size && size == old_cap && old_cap < new_cap &&
            PtrArray::seg(p, 0, size, l)
    Ensure __return != 0 &&
           PtrArray::seg(__return, 0, size, l) *
           PtrArray::undef_seg(__return, size, new_cap)
 */;

void minisat_ptr_array_free(void **p)
/*@ With size cap l
    Require 0 <= size && size <= cap &&
            PtrArray::seg(p, 0, size, l) *
            PtrArray::undef_seg(p, size, cap)
    Ensure emp
 */;

/* The `__return % 2 == 0` and `(__return & 1) == 0` conjuncts write out the
   arithmetic and native low-bit forms of the same "suitably aligned" promise;
   the low bit is unchanged by the native unsigned truncation.  This does not
   add allocator freshness or allocation-failure behavior.

   Why the evenness is reasonable: it is expected to be satisfied by memory
   alignment.  malloc returns storage suitably aligned for any object with a
   fundamental alignment (C17 7.22.3.1), i.e. aligned to _Alignof(max_align_t),
   which no hosted implementation makes smaller than 4.  struct clause_t needs
   only 4-byte alignment itself - an int, a float, and a flexible lit array -
   so a conforming allocator returns an address divisible by 4, hence even,
   on 32-bit and 64-bit hosts alike.  Both the verification arm's contract
   above and the native arm's bare malloc below therefore satisfy the evenness
   conjunct on every target this code supports.

   Note what this argument is NOT: it is a fact about the C implementation's
   allocator, not something the separation logic establishes.  The proof's
   memory model has its own pointer-alignment notion, but that constrains how
   pointer-typed storage is addressed - it says nothing about what malloc
   returns for a struct clause_t, and must not be read as discharging this.

   Why it matters: the low bit of a clause address is used as a tag (see
   clause_is_lit), so an odd clause address would silently misclassify a
   pointer as a literal and fabricate reason chains.  This is the one
   assumption in this file whose violation is a semantic failure rather than a
   crash.

   It nevertheless remains a trusted assumption: QCP does not prove it - the
   assert at clause_new is discharged from this very conjunct in the
   verification arm and is a debug-only check in the native build - so the
   platform allocator's alignment is taken on faith. */
struct clause_t *minisat_clause_alloc(int size)
/*@ Require size > 1 && emp
    Ensure __return != 0 && __return % 2 == 0 && (__return & 1) == 0 &&
           MiniSatClause::undef(__return, size)
 */;

void minisat_clause_free(struct clause_t *c)
/*@ With size
    Require MiniSatClause::owned(c, size)
    Ensure emp
 */;


/* --- Growth-path reallocation ---------------------------------------------
   [solver_setnvars] grows eight arrays that are LIVE up to [size] and
   UNINITIALISED from [size] to the old capacity.  The [_realloc] contracts
   above do NOT cover that shape: they require [size == old_cap], a
   completely full array, which is the only case [veci_reserve] ever reallocs
   (it grows only when [v->size == v->cap]).  An undefined tail cannot be
   promoted to a live segment -- [undef_seg] is built from uninitialised
   cells, not from [EX a, storeA] -- so a separate contract is required.

   Each contract names the WHOLE old block on the left, live prefix AND
   uninitialised tail, and returns the whole new block.  Understating the
   footprint would be UNSOUND: on a SECOND growth the shim would hand back a
   tail the caller is already holding, and the same memory would be owned
   twice.

   TRUSTED, like the rest of this file: `realloc` is not verified.  We assume
   the platform returns a non-null block suitably aligned for the element
   type (see the alignment note on minisat_clause_alloc above) whose first
   [size] elements hold the old contents.  Growth is the only caller.
 */
int *minisat_int_array_grow(int *p, int size, int old_cap, int new_cap)
/*@ With l
    Require 0 <= size && size <= old_cap && old_cap < new_cap &&
            new_cap <= INT_MAX &&
            IntArray::seg(p, 0, size, l) *
            IntArray::undef_seg(p, size, old_cap)
    Ensure __return != 0 &&
           IntArray::seg(__return, 0, size, l) *
           IntArray::undef_seg(__return, size, new_cap)
 */;

void **minisat_ptr_array_grow(void **p, int size, int old_cap, int new_cap)
/*@ With l
    Require 0 <= size && size <= old_cap && old_cap < new_cap &&
            new_cap <= INT_MAX &&
            PtrArray::seg(p, 0, size, l) *
            PtrArray::undef_seg(p, size, old_cap)
    Ensure __return != 0 &&
           PtrArray::seg(__return, 0, size, l) *
           PtrArray::undef_seg(__return, size, new_cap)
 */;

char *minisat_char_array_grow(char *p, int size, int old_cap, int new_cap)
/*@ With l
    Require 0 <= size && size <= old_cap && old_cap < new_cap &&
            new_cap <= INT_MAX &&
            CharArray::seg(p, 0, size, l) *
            CharArray::undef_seg(p, size, old_cap)
    Ensure __return != 0 &&
           CharArray::seg(__return, 0, size, l) *
           CharArray::undef_seg(__return, size, new_cap)
 */;

double *minisat_double_array_grow(double *p, int size, int old_cap, int new_cap)
/*@ With (l : list fp64)
    Require 0 <= size && size <= old_cap && old_cap < new_cap &&
            new_cap <= INT_MAX &&
            DoubleArray::seg(p, 0, size, l) *
            DoubleArray::undef_seg(p, size, old_cap)
    Ensure __return != 0 &&
           DoubleArray::seg(__return, 0, size, l) *
           DoubleArray::undef_seg(__return, size, new_cap)
 */;

/* The watcher table holds 2 in-place vecp structs per variable, so this one
   is indexed by [n] variables but sized [2*cap] slots.  It must be spelled in
   [wlists_rep] / [wlists_undef] vocabulary: QCP has no congruence closure, so
   an equivalent-looking variant would not match the caller's atoms. */
struct vecp_t *minisat_vecp_array_grow(struct vecp_t *p, int n,
                                       int old_cap, int new_cap)
/*@ With (wm : list (list Z)) (caps : list Z)
    Require 0 <= n && n <= old_cap && old_cap < new_cap &&
            2 * new_cap <= INT_MAX &&
            wlists_rep(p, n, wm, caps) *
            wlists_undef(p, 2 * n, 2 * old_cap)
    Ensure __return != 0 &&
           wlists_rep(__return, n, wm, caps) *
           wlists_undef(__return, 2 * n, 2 * new_cap)
 */;

#ifdef MINISAT_QCP_NATIVE_RUNTIME
void *malloc(unsigned long size);
void *realloc(void *ptr, unsigned long size);
void free(void *ptr);

#define minisat_solver_alloc() \
    ((struct solver_t *)malloc(sizeof(struct solver_t)))
#define minisat_int_array_alloc(cap) \
    ((int *)malloc(sizeof(int) * (cap)))
#define minisat_int_array_realloc(p, old_cap, new_cap) \
    ((int *)realloc((p), sizeof(int) * (new_cap)))
#define minisat_int_array_free(p) free(p)
#define minisat_ptr_array_alloc(cap) \
    ((void **)malloc(sizeof(void *) * (cap)))
#define minisat_ptr_array_realloc(p, old_cap, new_cap) \
    ((void **)realloc((p), sizeof(void *) * (new_cap)))
#define minisat_ptr_array_free(p) free(p)
#define minisat_clause_alloc(size) \
    ((struct clause_t *)malloc(sizeof(struct clause_t) + sizeof(lit) * (size)))
#define minisat_clause_free(c) free(c)
#define minisat_int_array_grow(p, size, old_cap, new_cap) \
    ((int *)realloc((p), sizeof(int) * (new_cap)))
#define minisat_ptr_array_grow(p, size, old_cap, new_cap) \
    ((void **)realloc((p), sizeof(void *) * (new_cap)))
#define minisat_char_array_grow(p, size, old_cap, new_cap) \
    ((char *)realloc((p), sizeof(char) * (new_cap)))
#define minisat_double_array_grow(p, size, old_cap, new_cap) \
    ((double *)realloc((p), sizeof(double) * (new_cap)))
#define minisat_vecp_array_grow(p, n, old_cap, new_cap) \
    ((struct vecp_t *)realloc((p), sizeof(vecp) * (new_cap) * 2))
#endif

/* The two random bodies (drand, irand) and the two solver_solve budget casts:
   the canonical QCP expression language has no double-to-int conversion (no fp64-to-Z;
   explicit `(int)x` is rejected and the implicit form fails type inference whenever the
   result is used). The frozen
   drand/irand bodies and the two solver_solve budget casts therefore sit behind audited
   external contracts on the canonical path. The random results are deliberately
   unconstrained beyond their ranges; the budget result is entirely unconstrained
   (restart/reduce scheduling is heuristic-only and cannot justify SAT or UNSAT). The
   seed cell keeps the exact integer-valued-double domain [1, 2147483646]; the
   integer-recurrence justification for the native random bodies is proved in the seed
   library (pure-Z shadow lemmas), making these audited dependencies, not proved native
   code.  The native budget facade preserves every defined nonnegative cast and
   saturates values above INT_MAX, avoiding the frozen recurrence's finite-prefix
   double-to-int undefined behavior without exposing heuristic scheduling to the proof. */
#ifndef MINISAT_QCP_NATIVE_RUNTIME
int minisat_uint64_sum_to_int(unsigned long long left,
                              unsigned long long right)
/*@ Require emp
    Ensure __return == MiniSatTarget::uint64_sum_to_int(left, right) && emp
 */;

int minisat_uint64_to_int(unsigned long long value)
/*@ Require emp
    Ensure __return == MiniSatTarget::signed_low32(value) && emp
 */;

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
#define minisat_uint64_sum_to_int(left, right) \
    ((int)((left) + (right)))
#define minisat_uint64_to_int(value) ((int)(value))

#define minisat_budget_to_int(x) \
    ((x) > 2147483647.0 ? 2147483647 : (int)(x))
#endif

void qcp_assert(int expr)
/*@ Require expr != 0 && emp
    Ensure emp
 */;
#define assert(expr) qcp_assert(expr)
