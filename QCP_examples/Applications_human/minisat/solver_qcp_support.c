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


/* Literal, clause, ordering, activity and database helpers. */
#include "solver_qcp_internal.h"

const bool  true      = 1;
const bool  false     = 0;
const int   var_Undef = -1;
const lit   lit_Undef = -2;
const lbool l_Undef   =  0;
const lbool l_True    =  1;
const lbool l_False   = -1;

// Random numbers:

// Canonical QCP cannot express these double-to-int operations, so it uses
// minisat_qcp_compat.h's trusted RNG contracts; these bodies are native-only.
#ifdef MINISAT_QCP_NATIVE_RUNTIME
static inline double drand(double* seed) {
    int q;
    *seed *= 1389796;
    q = (int)(*seed / 2147483647);
    *seed -= (double)q * 2147483647;
    return *seed / 2147483647; }

static inline int irand(double* seed, int size) {
    return (int)(drand(seed) * size); }
#endif


static void sort(void** array, int size)
/*@ sort_spec
    With (db : dbmap) (origin : list Z)
    Require 0 <= size && size <= INT_MAX && Zlength(origin) == size &&
            learnt_sort_domain(db, origin) && NoDup(db_words(db)) &&
            PtrArray::seg(array, 0, size, origin) * clause_db_rep(db)
    Ensure exists (current : list Z),
           Permutation(origin, current) && Zlength(current) == size &&
           PtrArray::seg(array, 0, size, current) * clause_db_rep(db)
 */;

lit  toLit   (int v)
/*@ default */
{ return v + v; }

lit  lit_neg (lit l)
/*@ bounded */
/*@ original */
/*@ sentinel */
{ return l ^ 1; }

int  lit_var (lit l)
/*@ bounded_index */
/*@ zero_index */
/*@ original */
{ return l >> 1; }

int  lit_sign(lit l)
/*@ default */
{ return (l & 1); }

static inline void check(int expr) /*@ Require expr != 0 && emp Ensure emp */
{ assert(expr); }

int minisat_simpdb_props_after_propagation(int value)
/*@ default */
{
    if (value == (-2147483647 - 1))
        return value;
    return value - 1;
}

int   clause_size       (clause* c)
/*@ default */
{ /*@ store(clause_hdr_addr(c), int, header)
       which implies store(&(c->size_learnt), int, header)
   */
  return c->size_learnt >> 1; }

lit*  clause_begin      (clause* c)
/*@ default */
{
  return c->lits; }

int   clause_learnt     (clause* c)
/*@ default */
{ /*@ store(clause_hdr_addr(c), int, header)
       which implies store(&(c->size_learnt), int, header)
   */
  return c->size_learnt & 1; }

static inline float clause_activity   (clause* c)
/*@ With size a
    Require 0 <= size &&
            store(clause_hdr_addr(c), int, clause_hdr_word(msat_true, size)) *
            store(clause_act_addr(c, size), float, a)
    Ensure msat_fp32_same(__return, a) &&
           store(clause_hdr_addr(c), int, clause_hdr_word(msat_true, size)) *
           store(clause_act_addr(c, size), float, a)
 */
{ /*@ 0 <= size &&
       store(clause_hdr_addr(c), int, clause_hdr_word(msat_true, size)) *
       store(clause_act_addr(c, size), float, a)
       which implies 0 <= clause_hdr_word(msat_true, size) &&
       store(&(c->size_learnt), int, clause_hdr_word(msat_true, size)) *
       store(&(c->lits[clause_hdr_word(msat_true, size) >> 1]), float, a)
   */
  return *((float*)&c->lits[c->size_learnt>>1]); }

static inline void  clause_setactivity(clause* c, float a)
/*@ With size old
    Require 0 <= size &&
            store(clause_hdr_addr(c), int, clause_hdr_word(msat_true, size)) *
            store(clause_act_addr(c, size), float, old)
    Ensure store(clause_hdr_addr(c), int, clause_hdr_word(msat_true, size)) *
           store(clause_act_addr(c, size), float, a)
 */
{ /*@ 0 <= size &&
       store(clause_hdr_addr(c), int, clause_hdr_word(msat_true, size)) *
       store(clause_act_addr(c, size), float, old)
       which implies 0 <= clause_hdr_word(msat_true, size) &&
       store(&(c->size_learnt), int, clause_hdr_word(msat_true, size)) *
       store(&(c->lits[clause_hdr_word(msat_true, size) >> 1]), float, old)
   */
  *((float*)&c->lits[c->size_learnt>>1]) = a; }

/* Binary reasons encode a literal in a pointer word with its low bit set;
   heap clause pointers have that bit clear. */
clause* clause_from_lit (lit l)
/*@ default */
{ return (clause*)((unsigned long)l + (unsigned long)l + 1);  }

bool    clause_is_lit   (clause* c)
/*@ default */
{ return ((unsigned long)c & 1);                              }

lit     clause_read_lit (clause* c)
/*@ default */
{ return (lit)((unsigned long)c >> 1);                        }

int     solver_dlevel(solver* s)
/*@ default */
{ return veci_size(&s->trail_lim); }

vecp*   solver_read_wlist     (solver* s, lit l)
/*@ default */
{ /*@ solver_wlists_handle(s, rdw_wl)
       which implies store(&(s->wlists), vecp *, rdw_wl)
   */
  return &s->wlists[l]; }

void order_update(solver* s, int v) // updateorder
/*@ default */
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
                   activity == activity_ptr &&
                   0 <= x && x < n &&
                   0 <= i && i < Zlength(heap_now) &&
                   parent == (i - 1) / 2 &&
                   0 <= parent && parent < Zlength(heap_now) &&
                   0 <= heap_now[parent - 0] &&
                   heap_now[parent - 0] < n &&
                   store(&(s->orderpos), int *, orderpos_ptr) *
                   store(&(s->activity), double *, activity_ptr) *
                   IntArray::seg(orderpos, 0, n, orderpos_now) *
                   Veci::rep_ptr(&(s->order), heap, heap_now) *
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

/* Assigned variables remain in the heap and are discarded lazily during
   selection. */
void order_assigned(solver* s, int v)
/*@ default */
{
}

void order_unassigned(solver* s, int v) // undoorder
/*@ default */
{
    /*@ order_unassigned_pre(n, v, heap0, orderpos0)
        which implies
          order_unassigned_pre(n, v, heap0, orderpos0) &&
          0 <= v && v < n &&
          2 * n <= INT_MAX &&
          (orderpos0[v - 0] != -1 || Zlength(heap0) < n)
     */
    int* orderpos = s->orderpos;
    if (orderpos[v] == -1){
        orderpos[v] = veci_size(&s->order);
        veci_push(&s->order,v);
        /*@ IntArray::full(
              orderpos, n,
              replace_Znth(v, Zlength(heap0), orderpos0))
            which implies
            IntArray::seg(
              orderpos, 0, n,
              replace_Znth(v, Zlength(heap0), orderpos0))
         */
        /*@ order_unassigned_pre(
              n, v, heap0, orderpos0) &&
            orderpos0[v] == -1
            which implies
            order_update_pre(
              n, v, app(heap0, cons(v, nil)),
              replace_Znth(v, Zlength(heap0), orderpos0))
         */
        order_update(s,v);
    }
}

/* Try a random unassigned variable, then fall back to the activity heap. */
int order_select(solver* s, float random_var_freq) // selectvar
/*@ default */
{
    /*@ order_select_pre(n, heap0, orderpos0, assigns0, trail0, qhead)
        which implies
          order_select_pre(n, heap0, orderpos0, assigns0, trail0, qhead) &&
          0 <= n && Zlength(assigns0) == n
     */
    int*    heap;
    double* activity;
    int*    orderpos;

    lbool* values = s->assigns;

    // Random decision:
    if (s->size > 0 &&
        drand(&s->random_seed)
          /*@ where z = seed_shadow */ < random_var_freq){
        /*@ Given seed_shadow_after_drand from z2 */
        int next = irand(&s->random_seed,s->size)
          /*@ where z = seed_shadow_after_drand */;
        assert(next >= 0 && next < s->size);
        /*@ 0 <= next && next < n by local */
        if (values[next] == l_Undef)
            return next;
    }

    // Activity based decision:

    heap     = veci_begin(&s->order);
    activity = s->activity;
    orderpos = s->orderpos;

    /*@ Inv Assert (exists heap_now orderpos_now seed_value_now seed_shadow_now,
                   s == s@pre &&
                   order_select_loop_inv(n, heap0, heap_now, orderpos_now,
                                         assigns0, trail0, qhead) &&
                   activity == activity_ptr &&
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
                   Veci::rep_ptr(&(s->order), heap, heap_now) *
                   has_permission(&random_var_freq)) *
          store(&l_Undef, char, 0) * store(&var_Undef, int, -1)
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

            /*@ Inv Assert (exists sift_heap_before sift_heap_now
                                 sift_orderpos_now
                                 sift_seed_value_now sift_seed_shadow_now,
                           s == s@pre &&
                           order_select_sift_inv(n, next, x, i,
                             heap0, sift_heap_before, sift_heap_now,
                             sift_orderpos_now,
                             assigns0, trail0, qhead) &&
                           Zlength(activity0) == n &&
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
                           Veci::rep_ptr(&(s->order), heap,
                                         sift_heap_now) *
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
                               activity0)))) *
          store(&l_Undef, char, 0) * store(&var_Undef, int, -1)
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

        if (values[next] == l_Undef)
            return next;
    }

    return var_Undef;
}

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

void act_var_bump(solver* s, int v)
/*@ default */
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
          Veci::rep(&(s->order), heap0) *
          store(&(s->var_inc), double, var_inc_now)
     */

    //printf("bump %d %f\n", v-1, activity[v]);

    if (s->orderpos[v] != -1)
        order_update(s,v);

}

void act_var_decay(solver* s)
/*@ default */
{ s->var_inc *= s->var_decay; }

static inline void act_clause_rescale(solver* s)
/*@ With (db : dbmap) cla_inc0
    Require learnt_db(db) && msat_fp32_nonnegative(cla_inc0) &&
            Vecp::rep(&(s->learnts), db_words(db)) *
            clause_db_rep(db) *
            store(&(s->cla_inc), cla_inc0)
    Ensure exists cla_inc1,
           msat_fp32_nonnegative(cla_inc1) &&
           Vecp::rep(&(s->learnts), db_words(db)) *
           clause_db_rep(db) *
           store(&(s->cla_inc), cla_inc1)
 */
{
    clause** cs = (clause**)vecp_begin(&s->learnts);
    int i;
    /*@ Inv Assert s == s@pre &&
                   0 <= i && i <= Zlength(db_words(db)) && learnt_db(db) &&
                   msat_fp32_nonnegative(cla_inc0) &&
                   Vecp::rep_ptr(&(s->learnts), cs, db_words(db)) *
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
              store(clause_act_addr(db_words(db)[i - 0], Zlength(clause_words)), float,
                    activity_now) *
              IntArray::seg(clause_lits_addr(db_words(db)[i - 0]), 0,
                            Zlength(clause_words), clause_words) *
              clause_db_pair_remainder(db_nil, db,
                                       db_words(db)[i - 0], msat_true,
                                       clause_words)
         */
        /*@ Given clause_words activity_now */
        float a = clause_activity(cs[i]);
        clause_setactivity(cs[i], a * (float)1e-20);
        /*@ exists (activity_after a_v : fp32),
            learnt_db(db) &&
            msat_fp32_nonnegative(activity_after) &&
            msat_fp32_nonnegative(a_v) &&
            0 < db_words(db)[i - 0] &&
            db_words(db)[i - 0] % 2 == 0 &&
            store(&a, float, a_v) *
            store(clause_hdr_addr(db_words(db)[i - 0]), int,
                  clause_hdr_word(msat_true, Zlength(clause_words))) *
            store(clause_act_addr(db_words(db)[i - 0], Zlength(clause_words)), float,
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
    s->cla_inc *= (float)1e-20;
}

void act_clause_bump(solver* s, clause *c)
/*@ default */
{
    /*@ learnt_db(db) && In(c, db_words(db)) && clause_db_rep(db)
        which implies exists (clause_words : list Z)
                             (activity_now : fp32),
          learnt_db(db) && In(c, db_words(db)) &&
          msat_fp32_nonnegative(activity_now) &&
          0 < c && c % 2 == 0 &&
          store(clause_hdr_addr(c), int,
                clause_hdr_word(msat_true, Zlength(clause_words))) *
          store(clause_act_addr(c, Zlength(clause_words)), float, activity_now) *
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
        store(clause_act_addr(c, Zlength(clause_words)), float, a_v) *
        IntArray::seg(clause_lits_addr(c), 0,
                      Zlength(clause_words), clause_words) *
        clause_db_pair_remainder(db_nil, db, c, msat_true, clause_words)
        which implies learnt_db(db) && In(c, db_words(db)) &&
                      msat_fp32_nonnegative(a_v) &&
                      store(&a, float, a_v) *
                      clause_db_rep(db)
     */
    if (a > 1e20) act_clause_rescale(s);
}

void act_clause_decay(solver* s)
/*@ default */
{ s->cla_inc *= s->cla_decay; }

/* Allocate a non-unit clause and install its two watches. The caller
   publishes it in the appropriate clause database. */
clause *clause_new(solver *s, lit *begin, lit *endvar, int learnt)
/*@ clause_new_spec */
{
    /*@ learnt == cn_sel && 0 <= cn_sel && cn_sel <= 1 &&
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
        which implies
          learnt == cn_sel && 0 <= cn_sel && cn_sel <= 1 &&
          endvar == begin + Zlength(cn_words) * sizeof(int) &&
          2 <= Zlength(cn_words) &&
          2 * Zlength(cn_words) + 1 <= INT_MAX &&
          cn_n == ms_size(cn_M) && solver_shape(cn_M) &&
          solver_support_inv(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_root, cn_M) &&
          ms_capacity_root_propagation_pending(cn_M) == 0 &&
          msolver_seed_shadow(cn_M) &&
          clause_install_pending_cert(cn_n, cn_F, msolver_set_root(cn_M, cn_root), cn_words, solver_selected_is_learnt(cn_sel)) &&
          Vecp::slot(cn_wl, lit_neg_c(cn_words[0 - 0])) !=
            Vecp::slot(cn_wl, lit_neg_c(cn_words[1 - 0])) &&
          store(&(s->size), cn_n) *
          solver_wlists_handle(s, cn_wl) *
          Vecp::rep(solver_selected_vec(s, cn_sel), db_words(solver_selected_db(cn_sel, cn_M))) *
          wlists_rep(cn_wl, cn_n, ms_wm(cn_M)) *
          clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
          clause_new_frame_at_gen(s, cn_M, lvl, cn_sel) *
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words)
     */
    /*@ 0 <= cn_sel && cn_sel <= 1 && endvar == begin + Zlength(cn_words) * sizeof(int) &&
          0 <= Zlength(cn_words) &&
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words)
        which implies
          endvar - begin == Zlength(cn_words) &&
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words)
     */
    int size;
    clause *c;
    int i;


    assert(endvar - begin > 1);
    assert(learnt >= 0 && learnt < 2);
    size = endvar - begin;

    /*@ 0 <= cn_sel && cn_sel <= 1 && 2 <= Zlength(cn_words) &&
        2 * Zlength(cn_words) + 1 <= INT_MAX &&
        Forall(lit_wf_c(cn_n), cn_words) &&
        NoDup(map(lit_var_c, cn_words)) &&
        solver_shape(cn_M) &&
          solver_support_inv(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_root, cn_M) &&
        ms_capacity_root_propagation_pending(cn_M) == 0 &&
        msolver_seed_shadow(cn_M) &&
        store(&(s->size), cn_n) *
        solver_wlists_handle(s, cn_wl) *
        Vecp::rep(solver_selected_vec(s, cn_sel), db_words(solver_selected_db(cn_sel, cn_M))) *
        wlists_rep(cn_wl, cn_n, ms_wm(cn_M)) *
        clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
        clause_new_frame_at_gen(s, cn_M, lvl, cn_sel) *
        IntArray::seg(begin, 0, Zlength(cn_words), cn_words)
        which implies
        exists (watch_words0 watch_words1 : list Z),
          2 <= Zlength(cn_words) &&
          2 * Zlength(cn_words) + 1 <= INT_MAX &&
          Forall(lit_wf_c(cn_n), cn_words) &&
          NoDup(map(lit_var_c, cn_words)) &&
          solver_shape(cn_M) &&
          solver_support_inv(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_root, cn_M) &&
          ms_capacity_root_propagation_pending(cn_M) == 0 &&
          msolver_seed_shadow(cn_M) &&
          watch_words0 == Znth(lit_neg_c(cn_words[0 - 0]),
                               ms_wm(cn_M), nil) &&
          watch_words1 == Znth(lit_neg_c(cn_words[1 - 0]),
                               ms_wm(cn_M), nil) &&
          Vecp::rep(solver_selected_vec(s, cn_sel), db_words(solver_selected_db(cn_sel, cn_M))) *
          Vecp::rep(Vecp::slot(cn_wl, lit_neg_c(cn_words[0 - 0])), watch_words0) *
          Vecp::rep(Vecp::slot(cn_wl, lit_neg_c(cn_words[1 - 0])), watch_words1) *
          clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
          clause_new_transaction_rest_at_gen(s, cn_wl,
            lit_neg_c(cn_words[0 - 0]),
            lit_neg_c(cn_words[1 - 0]), cn_M, lvl, cn_sel) *
          store(&(s->size), cn_n) *
          IntArray::seg(begin, 0, Zlength(cn_words), cn_words)
     */
    /*@ Given watch_words0 watch_words1 */

    c = minisat_clause_alloc(size, learnt);
    /*@ 0 <= cn_sel && cn_sel <= 1 && clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_M, cn_words, cn_sel, cn_root) &&
          MiniSatClause::undef(c, solver_selected_is_learnt(cn_sel), size) *
          clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
          clause_new_transaction_rest_at_gen(
            s, cn_wl,
            lit_neg_c(cn_words[0 - 0]),
            lit_neg_c(cn_words[1 - 0]), cn_M, lvl, cn_sel)
        which implies
          clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_M, cn_words, cn_sel, cn_root) &&
          clause_allocator_fresh(cn_M, c) &&
          MiniSatClause::undef(c, solver_selected_is_learnt(cn_sel), size) *
          clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
          clause_new_transaction_rest_at_gen(
            s, cn_wl,
            lit_neg_c(cn_words[0 - 0]),
            lit_neg_c(cn_words[1 - 0]), cn_M, lvl, cn_sel)
     */
    /*@ 0 <= cn_sel && cn_sel <= 1 && MiniSatClause::undef(c, solver_selected_is_learnt(cn_sel), size)
        which implies
          0 < c && c % 2 == 0 &&
          undef_data_at(&(c->size_learnt), int) *
          activity_undef(c, solver_selected_is_learnt(cn_sel), size) *
          IntArray::undef_seg(&(c->lits), 0, size)
     */
    c->size_learnt = (size << 1) | learnt;
    assert(((unsigned int)c & 1) == 0);

    /*@ Inv Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
                   0 <= i && i <= size &&
                   size == Zlength(cn_words) &&
                   learnt == cn_sel &&
                   watch_words0 ==
                     Znth(lit_neg_c(cn_words[0 - 0]),
                          ms_wm(cn_M), nil) &&
                   watch_words1 ==
                     Znth(lit_neg_c(cn_words[1 - 0]),
                          ms_wm(cn_M), nil) &&
                   cn_n == ms_size(cn_M) &&
                   2 <= Zlength(cn_words) &&
                   2 * Zlength(cn_words) + 1 <= INT_MAX &&
                   0 < c && c % 2 == 0 &&
                   clause_allocator_fresh(cn_M, c) &&
                   clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_M, cn_words, cn_sel, cn_root) &&
                   store(&(c->size_learnt), size * 2 + cn_sel) *
                   activity_undef(c, solver_selected_is_learnt(cn_sel), size) *
                   IntArray::seg(&(c->lits), 0, i,
                                 sublist(0, i, cn_words)) *
                   IntArray::undef_seg(&(c->lits), i, size) *
                   Vecp::rep(solver_selected_vec(s, cn_sel), db_words(solver_selected_db(cn_sel, cn_M))) *
                   Vecp::rep(Vecp::slot(cn_wl, lit_neg_c(cn_words[0 - 0])), watch_words0) *
                   Vecp::rep(Vecp::slot(cn_wl, lit_neg_c(cn_words[1 - 0])), watch_words1) *
                   clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
                   clause_new_transaction_rest_at_gen(s, cn_wl,
                     lit_neg_c(cn_words[0 - 0]),
                     lit_neg_c(cn_words[1 - 0]), cn_M, lvl, cn_sel) *
                   store(&(s->size), cn_n) *
                   IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
                   has_permission(&endvar)
     */
    for (i = 0; i < size; i++)
        c->lits[i] = begin[i];

    if (learnt)
        /*@ 0 <= cn_sel && cn_sel <= 1 && cn_sel != 0 &&
              activity_undef(c, solver_selected_is_learnt(cn_sel), size)
            which implies undef_data_at(&(c->lits[size]), float)
         */
        *((float*)&c->lits[size]) = 0.0;

    /*@ Assert 0 <= cn_sel && cn_sel <= 1 && s == s@pre && begin == begin@pre &&
                   i == size && size == Zlength(cn_words) && learnt == cn_sel && cn_n == ms_size(cn_M) &&
                   watch_words0 ==
                     Znth(lit_neg_c(cn_words[0 - 0]),
                          ms_wm(cn_M), nil) &&
                   watch_words1 ==
                     Znth(lit_neg_c(cn_words[1 - 0]),
                          ms_wm(cn_M), nil) &&
                   2 <= Zlength(cn_words) &&
                   2 * Zlength(cn_words) + 1 <= INT_MAX &&
                   2 * cn_n <= INT_MAX &&
                   0 <= Znth(0, cn_words, 0) &&
                   Znth(0, cn_words, 0) < 2 * cn_n &&
                   0 <= Znth(1, cn_words, 0) &&
                   Znth(1, cn_words, 0) < 2 * cn_n &&
                   0 <= lit_neg_c(cn_words[0 - 0]) &&
                   lit_neg_c(cn_words[0 - 0]) < 2 * cn_n &&
                   0 <= lit_neg_c(cn_words[1 - 0]) &&
                   lit_neg_c(cn_words[1 - 0]) < 2 * cn_n &&
                   0 < c && c % 2 == 0 &&
                   clause_allocator_fresh(cn_M, c) &&
                   clause_new_stage_ready_root(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_M, cn_words, cn_sel, cn_root) &&
                   MiniSatClause::rep(c, solver_selected_is_learnt(cn_sel), cn_words) *
                   Vecp::rep(solver_selected_vec(s, cn_sel), db_words(solver_selected_db(cn_sel, cn_M))) *
                   Vecp::rep(Vecp::slot(cn_wl, lit_neg_c(cn_words[0 - 0])), watch_words0) *
                   Vecp::rep(Vecp::slot(cn_wl, lit_neg_c(cn_words[1 - 0])), watch_words1) *
                   clause_db_rep(solver_selected_db(cn_sel, cn_M)) *
                   clause_new_transaction_rest_at_gen(s, cn_wl,
                     lit_neg_c(cn_words[0 - 0]),
                     lit_neg_c(cn_words[1 - 0]), cn_M, lvl, cn_sel) *
                   store(&(s->size), cn_n) *
                   IntArray::seg(begin, 0, Zlength(cn_words), cn_words) *
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


    /*@ clause_new_transaction_rest_at_gen(s, cn_wl,
          lit_neg_c(cn_words[0 - 0]), lit_neg_c(cn_words[1 - 0]), cn_M, lvl, cn_sel)
        which implies
          solver_wlists_handle(s, cn_wl) *
          VecpArray::missing2(cn_wl, lit_neg_c(cn_words[0 - 0]),
            lit_neg_c(cn_words[1 - 0]), 2 * ms_size(cn_M), ms_wm(cn_M)) *
          clause_new_frame_at_gen(s, cn_M, lvl, cn_sel)
     */
    vecp_push(solver_read_wlist(s, lit_neg(begin[0]) /*@ where (original) */)
                /*@ where rdw_wl = cn_wl */,
              (void *)(size > 2 ? c : clause_from_lit(begin[1])));
    vecp_push(solver_read_wlist(s, lit_neg(begin[1]) /*@ where (original) */)
                /*@ where rdw_wl = cn_wl */,
              (void *)(size > 2 ? c : clause_from_lit(begin[0])));
    /*@ solver_wlists_handle(s, cn_wl) *
          VecpArray::missing2(cn_wl, lit_neg_c(cn_words[0 - 0]),
            lit_neg_c(cn_words[1 - 0]), 2 * ms_size(cn_M), ms_wm(cn_M)) *
          clause_new_frame_at_gen(s, cn_M, lvl, cn_sel)
        which implies
          clause_new_transaction_rest_at_gen(s, cn_wl,
            lit_neg_c(cn_words[0 - 0]), lit_neg_c(cn_words[1 - 0]), cn_M, lvl, cn_sel)
     */
    return c;
}

/* Detach both watches and free an unlocked clause. Live propagation reasons
   must retain their clauses. */
void clause_remove(solver* s, clause* c)
/*@ default */
{
    /*@ clause_remove_pre(s, c, n, cap, wl, reasons_ptr, wm,
                          is_learnt, clause_words, stats0, reasons0)
        which implies
          0 <= n && n <= cap && 2 * n <= INT_MAX &&
          0 < c && c % 2 == 0 &&
          Zlength(reasons0) == n &&
          clause_remove_ready(n, c, clause_words, wm, stats0) &&
          clause_unlocked_words(c, reasons0) &&
          clause_remove_open_at(s, n, cap, wl, reasons_ptr, wm,
                                stats0, reasons0) *
          store(clause_hdr_addr(c), int,
                clause_hdr_word(is_learnt, Zlength(clause_words))) *
          activity_state(c, is_learnt, Zlength(clause_words)) *
          IntArray::seg(clause_lits_addr(c), 0, Zlength(clause_words),
                        clause_words)
     */
    lit* lits = clause_begin(c);
    /*@ Assert s == s@pre && c == c@pre &&
          lits == clause_lits_addr(c) &&
          0 <= n && n <= cap && 2 * n <= INT_MAX &&
          0 < c && c % 2 == 0 &&
          Zlength(reasons0) == n &&
          clause_remove_ready(n, c, clause_words, wm, stats0) &&
          clause_unlocked_words(c, reasons0) &&
          0 <= Znth(0, clause_words, 0) &&
          Znth(0, clause_words, 0) < 2 * n &&
          0 <= Znth(1, clause_words, 0) &&
          Znth(1, clause_words, 0) < 2 * n &&
          0 <= lit_neg_c(Znth(0, clause_words, 0)) &&
          lit_neg_c(Znth(0, clause_words, 0)) < 2 * n &&
          0 <= lit_neg_c(Znth(1, clause_words, 0)) &&
          lit_neg_c(Znth(1, clause_words, 0)) < 2 * n &&
          clause_remove_open_at(s, n, cap, wl, reasons_ptr, wm,
                                stats0, reasons0) *
          store(clause_hdr_addr(c), int,
                clause_hdr_word(is_learnt, Zlength(clause_words))) *
          activity_state(c, is_learnt, Zlength(clause_words)) *
          store(lits + 0 * sizeof(int), int,
                Znth(0, clause_words, 0)) *
          store(lits + 1 * sizeof(int), int,
                Znth(1, clause_words, 0)) *
          IntArray::seg(lits, 2, Zlength(clause_words),
                        sublist(2, Zlength(clause_words), clause_words))
     */
    assert(lit_neg(lits[0]) /*@ where(original) */ < s->size*2);
    assert(lit_neg(lits[1]) /*@ where(original) */ < s->size*2);

    //vecp_remove(solver_read_wlist(s,lit_neg(lits[0])),(void*)c);
    //vecp_remove(solver_read_wlist(s,lit_neg(lits[1])),(void*)c);

    assert(lits[0] < s->size*2);
    vecp_remove(solver_read_wlist(s,lit_neg(lits[0]) /*@ where (original) */),
                (void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[1])));
    vecp_remove(solver_read_wlist(s,lit_neg(lits[1]) /*@ where (original) */),
                (void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[0])));

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
          activity_state(c, is_learnt, Zlength(clause_words)) *
          store(lits + 0 * sizeof(int), int,
                Znth(0, clause_words, 0)) *
          store(lits + 1 * sizeof(int), int,
                Znth(1, clause_words, 0)) *
          IntArray::seg(lits, 2, Zlength(clause_words),
                        sublist(2, Zlength(clause_words), clause_words))
        which implies
          MiniSatClause::owned(c, is_learnt, Zlength(clause_words)) *
          has_permission(&lits)
     */
    minisat_clause_free(c);

}

lbool clause_simplify(solver* s, clause* c)
/*@ default */
{
    lit*   lits   = clause_begin(c);
    lbool* values = s->assigns;
    int i;

    assert(solver_dlevel(s) == 0);

    /*@ Inv Assert (s == s@pre && c == c@pre &&
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
                   activity_state(c, is_learnt, Zlength(clause_words)) *
                   IntArray::seg(lits, 0,
                                 Zlength(clause_words), clause_words) *
                   Veci::rep(&(s->trail_lim), z_nil)) *
          store(&l_True, char, 1) * store(&l_False, char, -1)
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
        sig += sig - 1;
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
        if (values[lit_var(lits[i]) /*@ where(original) */] == sig)

            return l_True;
    }

    return l_False;
}

/* Binary clauses sort last; other learned clauses compare by activity. */
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
              store(clause_act_addr(x, Zlength(x_words)), float, x_activity) *
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
              store(clause_act_addr(x, Zlength(x_words)), float, x_activity) *
              IntArray::seg(clause_lits_addr(x), 0,
                            Zlength(x_words), x_words) *
              store(clause_hdr_addr(y), int,
                    clause_hdr_word(msat_true, Zlength(y_words))) *
              store(clause_act_addr(y, Zlength(y_words)), float, y_activity) *
              IntArray::seg(clause_lits_addr(y), 0,
                            Zlength(y_words), y_words) *
              learnt_sort_two_remainder(
                db, activities,
                x, x_words, x_activity,
                y, y_words, y_activity)))
     */
    return clause_size((clause*)x) > 2 && (clause_size((clause*)y) == 2 || clause_activity((clause*)x) < clause_activity((clause*)y)) ? -1 : 1; }

void solver_reducedb(solver* s)
/*@ default */
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
          wlists_rep(wl, ms_size(M), ms_wm(M)) *
          store(&(s->reasons), reasons_ptr) *
          PtrArray::seg(reasons_ptr, 0, ms_size(M), ms_reason_words(M)) *
          solver_ptr_tail(reasons_ptr, ms_size(M), ms_cap(M)) *
          Vecp::rep(&(s->learnts), db_words(ms_learnt(M))) *
          clause_db_rep(ms_learnt(M)) *
          stats_rep(&(s->stats), ms_stats(M)) *
          solver_db_mutation_frame_at(s, M, levels_ptr)
     */
    /*@ Given reasons_ptr */
    int      i, j;
    double   extra_lim = s->cla_inc / vecp_size(&s->learnts); // Remove any clause below this activity
    clause** learnts = (clause**)vecp_begin(&s->learnts);
    clause** reasons = s->reasons;

    sort(vecp_begin(&s->learnts), vecp_size(&s->learnts));
    /*@ Given words_sorted from current */

    /*@ msolver_inv(n, F, A_arr, A_inst, M) &&
          mt_qhead(ms_core(M)) == ms_qtail(M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          learnt_sort_domain(ms_learnt(M), db_words(ms_learnt(M))) &&
          NoDup(db_words(ms_learnt(M))) &&
          Permutation(db_words(ms_learnt(M)), words_sorted) &&
          msat_fp64_count_limit(
            Zlength(db_words(ms_learnt(M))), extra_lim) &&
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
          msat_fp64_count_limit(Zlength(words_sorted), extra_lim) &&
          clause_db_rep(ms_learnt(Msorted))
     */

    j = 0;
    /*@ Inv Assert exists (Mcur : msolver) (words : list Z),
          s == s@pre &&
          solver_reducedb_loop_state(n, F, A_arr, A_inst, M, Mcur,
                                    words, i, j, extra_lim) &&
          reasons == reasons_ptr &&
          0 <= j && j <= i && i <= Zlength(words) &&
          store(&(s->size), ms_size(Mcur)) *
          store(&(s->cla_inc), ms_cla_inc(Mcur)) *
          store(&(s->wlists), wl) *
          wlists_rep(wl, ms_size(Mcur), ms_wm(Mcur)) *
          store(&(s->reasons), reasons_ptr) *
          PtrArray::seg(reasons_ptr, 0, ms_size(Mcur),
                        ms_reason_words(Mcur)) *
          solver_ptr_tail(reasons_ptr, ms_size(Mcur), ms_cap(Mcur)) *
          Vecp::rep_ptr(&(s->learnts), learnts, words) *
          clause_db_rep(ms_learnt(Mcur)) *
          stats_rep(&(s->stats), ms_stats(Mcur)) *
          solver_db_mutation_frame_at(s, Mcur, levels_ptr)
     */
    for (i = 0; i < vecp_size(&s->learnts) / 2; i++){
        /*@ Given Mcur words */
        /*@ db_compaction_inv(Mcur, words, i, j) &&
            msat_fp64_count_limit(Zlength(words), extra_lim) &&
            msolver_inv(n, F, A_arr, A_inst, Mcur) &&
            msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
            0 <= i && i < Zlength(words) &&
            clause_db_rep(ms_learnt(Mcur))
            which implies exists (lits_now : list Z)
                                 (activity_now : fp32),
              db_compaction_inv(Mcur, words, i, j) &&
              msat_fp64_count_limit(Zlength(words), extra_lim) &&
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
              store(clause_act_addr(words[i - 0], Zlength(lits_now)), float, activity_now) *
              IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                            Zlength(lits_now), lits_now) *
              clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                       words[i - 0], msat_true, lits_now)
         */
        /*@ Given lits_now activity_now */
        if (clause_size(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i])) /*@ where(original) */] != learnts[i])
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp64_count_limit(Zlength(words), extra_lim) &&
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
                solver_ptr_tail(reasons_ptr, ms_size(Mcur), ms_cap(Mcur)) *
                store(&(s->wlists), wl) *
                wlists_rep(wl, ms_size(Mcur), ms_wm(Mcur)) *
                store(clause_hdr_addr(words[i - 0]), int,
                      clause_hdr_word(msat_true, Zlength(lits_now))) *
                store(clause_act_addr(words[i - 0], Zlength(lits_now)), float, activity_now) *
                IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                              Zlength(lits_now), lits_now) *
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                stats_rep(&(s->stats), ms_stats(Mcur))
                which implies
                  db_compaction_inv(Mcur, words, i, j) &&
                  msat_fp64_count_limit(Zlength(words), extra_lim) &&
                  msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                  0 <= j && j <= i &&
                  clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                           words[i - 0], msat_true,
                                           lits_now) *
                  clause_remove_pre(
                    s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), wl,
                    reasons_ptr, ms_wm(Mcur), msat_true,
                    lits_now, ms_stats(Mcur), ms_reason_words(Mcur))
             */
            clause_remove(s,learnts[i]);
        else {
            learnts[j] = learnts[i];
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp64_count_limit(Zlength(words), extra_lim) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                msat_fp32_nonnegative(activity_now) &&
                0 <= j && j <= i && i < Zlength(words) &&
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                store(clause_hdr_addr(words[i - 0]), int,
                      clause_hdr_word(msat_true, Zlength(lits_now))) *
                store(clause_act_addr(words[i - 0], Zlength(lits_now)), float, activity_now) *
                IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                              Zlength(lits_now), lits_now)
                which implies
                  msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                  db_compaction_inv(Mcur,
                    replace_Znth(j, words[i - 0], words), i + 1, j + 1) &&
                  msat_fp64_count_limit(
                    Zlength(replace_Znth(j, words[i - 0], words)),
                    extra_lim) &&
                  0 <= j && j <= i && i < Zlength(words) &&
                  clause_db_rep(ms_learnt(Mcur))
             */
            j++;
        }
        /*@ Assert exists (Mnext : msolver) (words_next : list Z),
              s == s@pre &&
              db_compaction_step(Mcur, words[i - 0], Mnext) &&
              solver_reducedb_loop_state(n, F, A_arr, A_inst, M, Mnext,
                                    words_next, i + 1, j, extra_lim) &&
              reasons == reasons_ptr &&
              store(&(s->size), ms_size(Mnext)) *
              store(&(s->cla_inc), ms_cla_inc(Mnext)) *
              store(&(s->wlists), wl) *
              wlists_rep(wl, ms_size(Mnext), ms_wm(Mnext)) *
              store(&(s->reasons), reasons_ptr) *
              PtrArray::seg(reasons_ptr, 0, ms_size(Mnext),
                            ms_reason_words(Mnext)) *
              solver_ptr_tail(reasons_ptr, ms_size(Mnext), ms_cap(Mnext)) *
              Vecp::rep_ptr(&(s->learnts), learnts, words_next) *
              clause_db_rep(ms_learnt(Mnext)) *
              stats_rep(&(s->stats), ms_stats(Mnext)) *
              solver_db_mutation_frame_at(s, Mnext, levels_ptr)
         */
    }
    /*@ Inv Assert exists (Mcur : msolver) (words : list Z),
          s == s@pre &&
          solver_reducedb_loop_state(n, F, A_arr, A_inst, M, Mcur,
                                    words, i, j, extra_lim) &&
          reasons == reasons_ptr &&
          0 <= j && j <= i && i <= Zlength(words) &&
          store(&(s->size), ms_size(Mcur)) *
          store(&(s->cla_inc), ms_cla_inc(Mcur)) *
          store(&(s->wlists), wl) *
          wlists_rep(wl, ms_size(Mcur), ms_wm(Mcur)) *
          store(&(s->reasons), reasons_ptr) *
          PtrArray::seg(reasons_ptr, 0, ms_size(Mcur),
                        ms_reason_words(Mcur)) *
          solver_ptr_tail(reasons_ptr, ms_size(Mcur), ms_cap(Mcur)) *
          Vecp::rep_ptr(&(s->learnts), learnts, words) *
          clause_db_rep(ms_learnt(Mcur)) *
          stats_rep(&(s->stats), ms_stats(Mcur)) *
          solver_db_mutation_frame_at(s, Mcur, levels_ptr)
     */
    for (; i < vecp_size(&s->learnts); i++){
        /*@ Given Mcur words */
        /*@ db_compaction_inv(Mcur, words, i, j) &&
            msat_fp64_count_limit(Zlength(words), extra_lim) &&
            msolver_inv(n, F, A_arr, A_inst, Mcur) &&
            msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
            0 <= i && i < Zlength(words) &&
            clause_db_rep(ms_learnt(Mcur))
            which implies exists (lits_now : list Z)
                                 (activity_now : fp32),
              db_compaction_inv(Mcur, words, i, j) &&
              msat_fp64_count_limit(Zlength(words), extra_lim) &&
              msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
              msat_fp64_nonnegative(extra_lim) &&
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
              store(clause_act_addr(words[i - 0], Zlength(lits_now)), float, activity_now) *
              IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                            Zlength(lits_now), lits_now) *
              clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                       words[i - 0], msat_true, lits_now)
         */
        /*@ Given lits_now activity_now */
        if (clause_size(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i])) /*@ where(original) */] != learnts[i] && clause_activity(learnts[i]) < extra_lim)
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp64_count_limit(Zlength(words), extra_lim) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                msat_fp64_nonnegative(extra_lim) &&
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
                solver_ptr_tail(reasons_ptr, ms_size(Mcur), ms_cap(Mcur)) *
                store(&(s->wlists), wl) *
                wlists_rep(wl, ms_size(Mcur), ms_wm(Mcur)) *
                store(clause_hdr_addr(words[i - 0]), int,
                      clause_hdr_word(msat_true, Zlength(lits_now))) *
                store(clause_act_addr(words[i - 0], Zlength(lits_now)), float, activity_now) *
                IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                              Zlength(lits_now), lits_now) *
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                stats_rep(&(s->stats), ms_stats(Mcur))
                which implies
                  db_compaction_inv(Mcur, words, i, j) &&
                  msat_fp64_count_limit(Zlength(words), extra_lim) &&
                  msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                  0 <= j && j <= i &&
                  clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                           words[i - 0], msat_true,
                                           lits_now) *
                  clause_remove_pre(
                    s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), wl,
                    reasons_ptr, ms_wm(Mcur), msat_true,
                    lits_now, ms_stats(Mcur), ms_reason_words(Mcur))
             */
            clause_remove(s,learnts[i]);
        else {
            learnts[j] = learnts[i];
            /*@ msolver_inv(n, F, A_arr, A_inst, Mcur) &&
                db_compaction_inv(Mcur, words, i, j) &&
                msat_fp64_count_limit(Zlength(words), extra_lim) &&
                msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                msat_fp32_nonnegative(activity_now) &&
                0 <= j && j <= i && i < Zlength(words) &&
                clause_db_pair_remainder(db_nil, ms_learnt(Mcur),
                                         words[i - 0], msat_true, lits_now) *
                store(clause_hdr_addr(words[i - 0]), int,
                      clause_hdr_word(msat_true, Zlength(lits_now))) *
                store(clause_act_addr(words[i - 0], Zlength(lits_now)), float, activity_now) *
                IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                              Zlength(lits_now), lits_now)
                which implies
                  msat_fp32_same(ms_cla_decay(Mcur), ms_cla_decay(M)) &&
                  db_compaction_inv(Mcur,
                    replace_Znth(j, words[i - 0], words), i + 1, j + 1) &&
                  msat_fp64_count_limit(
                    Zlength(replace_Znth(j, words[i - 0], words)),
                    extra_lim) &&
                  0 <= j && j <= i && i < Zlength(words) &&
                  clause_db_rep(ms_learnt(Mcur))
             */
            j++;
        }
        /*@ Assert exists (Mnext : msolver) (words_next : list Z),
              s == s@pre &&
              db_compaction_step(Mcur, words[i - 0], Mnext) &&
              solver_reducedb_loop_state(n, F, A_arr, A_inst, M, Mnext,
                                    words_next, i + 1, j, extra_lim) &&
              reasons == reasons_ptr &&
              store(&(s->size), ms_size(Mnext)) *
              store(&(s->cla_inc), ms_cla_inc(Mnext)) *
              store(&(s->wlists), wl) *
              wlists_rep(wl, ms_size(Mnext), ms_wm(Mnext)) *
              store(&(s->reasons), reasons_ptr) *
              PtrArray::seg(reasons_ptr, 0, ms_size(Mnext),
                            ms_reason_words(Mnext)) *
              solver_ptr_tail(reasons_ptr, ms_size(Mnext), ms_cap(Mnext)) *
              Vecp::rep_ptr(&(s->learnts), learnts, words_next) *
              clause_db_rep(ms_learnt(Mnext)) *
              stats_rep(&(s->stats), ms_stats(Mnext)) *
              solver_db_mutation_frame_at(s, Mnext, levels_ptr)
         */
    }

    //printf("reducedb deleted %d\n", vecp_size(&s->learnts) - j);

    vecp_resize(&s->learnts,j);
}

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

/* Randomized quicksort with selection-sort fallback. */
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

        /* The outer partition invariant has stopping indices strictly beyond
           the current cursors: i < L < size with L <= j, and 0 <= R < j.
           They bound the next scans; size <= INT_MAX also bounds cursor
           arithmetic. */
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

        for (;;) {
            do i++;
            /* This cut follows i++. Use the invariant at i-1 so its stopper
               may equal i; the valid read bound is i < size, including the
               last element. */
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
            /* This cut follows j--. Use the right-scan invariant at j+1 so
               its stopper may equal j; index 0 is a valid stopping point. */
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

        /*@ PtrArray::seg(array, i, size, right)
            which implies
              PtrArray::seg(
                pointer_offset(array, i, void *),
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
                pointer_offset(array, i, void *),
                0, size - i, right_after) *
              learnt_sort_rep(srt_db, srt_activities) *
              store(seed, seed_after_right) * has_permission(&tmp)
         */
        /*@ Given right_after seed_after_right shadow_after_right */
        /*@ PtrArray::seg(
              pointer_offset(array, i, void *),
              0, size - i, right_after)
            which implies PtrArray::seg(array, i, size, right_after)
         */

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

static void sort(void** array, int size)
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
