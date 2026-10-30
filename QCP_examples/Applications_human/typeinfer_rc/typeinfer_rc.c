/* Reference-counted type inference restart on current main.
 * The public mathematical contract is inherited from typeinfer.c.
 * User-approved shared M parameters connect all representation views.
 * copy_atype is retain; free_atype releases child edges on the final reference.
 * free_atype_node is the raw allocator boundary, not an assumed RC operation.
 */

#include "typeinfer_rc.h"
/*@ Import Coq Require Import SimpleC.EE.Applications_human.typeinfer_rc.typeinfer_rc_lib */
/*@ include strategies "typeinfer_rc.strategies" */

void free_atype_node(struct atype *t)
/*@ With (n : TypeNode)
    Require store(&(t->refcnt), int, 0) * store_node_payload(t, n)
    Ensure emp
*/;


struct atype *res[100];

struct atype *get_map(int n)
/*@ With (M : RcState) (s : sol)
    Require 0 <= n && n < 100 && store_solution(M, res, s)
    Ensure store_solution(M, res, s) &&
      ((__return == 0 && (forall tr, !solution_at(s, n, tr))) ||
       (__return != 0 && exists tr, solution_at(s, n, tr) &&
          store_type(M, __return, tr)))
*/
;

void add_map(int n, struct atype *t)
/*@ With (M : RcState) (M_old : RcState) (s : sol) (p : Z) (tr : TypeTree)
    Require 0 <= n && n < 100 &&
      (forall old, !solution_at(s, n, old)) &&
      not_occur_final(s, n, tr) && store_type(M, t, tr) &&
      rc_valid(M) && node_at(M, p, Node(3, n, 0)) &&
      retain_rel(M_old, t, M) && rc_reserved(M, t) > 0 &&
      store_solution(M_old, res, s) *
      store(&(p->d.VAR.name), int, n) *
      store_world_missing(M, payload_keys(p, Node(3, n, 0)))
    Ensure store_type(M, t, tr) &&
      rc_valid(rc_publish(M, t)) && rc_preserves(M_old, rc_publish(M, t)) &&
      rc_reservations_same(M_old, rc_publish(M, t)) &&
      store_world(rc_publish(M, t)) * store_solution(rc_publish(M, t), res, sol_update(s, n, tr))
*/
;

/* Under rc_valid, absent nodes have count zero. A positive count therefore
 * supplies node liveness without an existential witness in Require. */
struct atype *copy_atype(struct atype *t)
/*@ nonnull With (M : RcState)
    Require t != 0 && rc_valid(M) &&
      0 < rc_count(M, t) && rc_count(M, t) < 2147483647 &&
      store_world(M)
    Ensure exists M_post,
      __return == t && retain_rel(M, t, M_post) &&
      rc_valid(M_post) && rc_preserves(M, M_post) && store_world(M_post)
*/
/*@ null With (M : RcState)
    Require t == 0 && rc_valid(M) && store_world(M)
    Ensure exists M_post,
      __return == t && retain_rel(M, t, M_post) &&
      rc_valid(M_post) && rc_preserves(M, M_post) && store_world(M_post)
*/;

struct atype *copy_atype(struct atype *t)
/*@ nonnull */
/*@ null */
{
  if (t != 0) {
    t->refcnt = t->refcnt + 1;
  }
  return t;
}

struct atype *copy_atype(struct atype *t)
/*@ open_var <= nonnull
    With (M : RcState) (p : Z) (v : Z)
    Require rc_valid(M) && 0 < rc_count(M, t) &&
      rc_count(M, t) < 2147483647 && node_at(M, p, Node(3, v, 0)) &&
      store(&(p->d.VAR.name), int, v) *
      store_world_missing(M, payload_keys(p, Node(3, v, 0)))
    Ensure exists M_post,
      __return == t && retain_rel(M, t, M_post) &&
      rc_valid(M_post) && rc_preserves(M, M_post) &&
      store(&(p->d.VAR.name), int, v) *
      store_world_missing(M_post, payload_keys(p, Node(3, v, 0)))
*/;

/* The null and nonnull entry cases are verified independently. Under rc_valid,
 * reserved <= roots and absent nodes have roots zero, so a positive reserved
 * credit already implies liveness. No extra logical alias for t is needed. */
void free_atype(struct atype *t)
/*@ nonnull With (M : RcState)
    Require t != 0 && rc_valid(M) && rc_reserved(M, t) > 0 && store_world(M)
    Ensure exists M_post,
      release_rel(M, t, M_post) && rc_valid(M_post) && store_world(M_post)
*/
/*@ null With (M : RcState)
    Require t == 0 && rc_valid(M) && store_world(M)
    Ensure exists M_post,
      release_rel(M, t, M_post) && rc_valid(M_post) && store_world(M_post)
*/;

void free_atype(struct atype *t)
/*@ nonnull */
/*@ null */
{
  if (t == 0) {
    return;
  }
  t->refcnt = t->refcnt - 1;
  if (t->refcnt == 0) {
    if (t->t == AT_ARROW) {
      /*@ exists n, rc_valid(M_nonnull) && node_at(M_nonnull, t, n) &&
            rc_count(M_nonnull, t) == 1 && rc_reserved(M_nonnull, t) > 0 && node_tag(n) == 1 &&
            store_world_missing(M_nonnull, cons(field_key(t, Tag), cons(field_key(t, RefCount), nil)))
            which implies
          node_tag(n) == 1 && rc_valid(rc_delete(M_nonnull, t, n)) &&
          store(&(t->d.ARROW.from), struct atype *, node_a(n)) *
          store(&(t->d.ARROW.to), struct atype *, node_b(n)) *
          store_world(rc_delete(M_nonnull, t, n))
      */
      free_atype(t->d.ARROW.from) /*@ where(nonnull) */;
      free_atype(t->d.ARROW.to) /*@ where(nonnull) */;
    } else if (t->t == AT_APP) {
      /*@ exists n, rc_valid(M_nonnull) && node_at(M_nonnull, t, n) &&
            rc_count(M_nonnull, t) == 1 && rc_reserved(M_nonnull, t) > 0 && node_tag(n) == 2 &&
            store_world_missing(M_nonnull, cons(field_key(t, Tag), cons(field_key(t, RefCount), nil)))
            which implies
          node_tag(n) == 2 && rc_valid(rc_delete(M_nonnull, t, n)) &&
          store(&(t->d.APP.tfn), struct atype *, node_a(n)) *
          store(&(t->d.APP.rand), struct atype *, node_b(n)) *
          store_world(rc_delete(M_nonnull, t, n))
      */
      free_atype(t->d.APP.tfn) /*@ where(nonnull) */;
      free_atype(t->d.APP.rand) /*@ where(nonnull) */;
    }
    /* This semantic release checkpoint is not a view-only fold. */
    /*@ Assert exists M_post n,
          t == t@pre &&
          release_rel(M_nonnull, t, M_post) && rc_valid(M_post) &&
          store_world(M_post) * store(&(t->refcnt), int, 0) *
          store_node_payload(t, n) $ nonnull
    */
    free_atype_node(t);
  }
}

int type_var_occur(int v, struct atype *t)
/*@ With (M : RcState) (s : sol) (p : Z) (tr : TypeTree)
    Require 0 <= v && v < 100 && store_type(M, t, tr) &&
      rc_valid(M) && node_at(M, p, Node(3, v, 0)) &&
      store(&(p->d.VAR.name), int, v) *
      store_world_missing(M, payload_keys(p, Node(3, v, 0))) * store_solution(M, res, s)
    Ensure
      (__return == 0 && not_occur_final(s, v, tr) &&
        store(&(p->d.VAR.name), int, v) *
        store_world_missing(M, payload_keys(p, Node(3, v, 0))) * store_solution(M, res, s))
      ||
      (__return != 0 &&
        store(&(p->d.VAR.name), int, v) *
        store_world_missing(M, payload_keys(p, Node(3, v, 0))) * store_solution(M, res, s))
*/
;

/* The returned representative is chosen by this external helper, not by its
 * caller. Therefore capacity must hold for every admissible representative;
 * the guarded universal condition below cannot be replaced by one With-bound
 * output pointer. The With-bound tr only describes the existing solution slot.
 */
struct atype *atype_repr(int n)
/*@ With (M : RcState) (s : sol) (p : Z) (tr : TypeTree)
    Require 0 <= n && n < 100 && rc_valid(M) &&
      node_at(M, p, Node(3, n, 0)) &&
      solution_at(s, n, tr) &&
      (forall q out_tr, (store_type(M, q, out_tr) && repr_rel_node(s, TVar(n), out_tr)) =>
        rc_count(M, q) < 2147483647) &&
      store(&(p->d.VAR.name), int, n) *
      store_world_missing(M, payload_keys(p, Node(3, n, 0))) *
      store_solution(M, res, s)
    Ensure exists M_post tr_out,
      repr_result(M, s, n, __return, M_post) && rc_valid(M_post) &&
      rc_preserves(M, M_post) && store_type(M_post, __return, tr_out) &&
      repr_rel_node(s, TVar(n), tr_out) &&
      retain_rel(M, __return, M_post) &&
      store_world(M_post) * store_solution(M_post, res, s)
*/
;

int atype_unify1(struct atype *t1, struct atype *t2)
/*@ With (M : RcState) (s : sol) (tr1 : TypeTree) (tr2 : TypeTree)
    Require rc_valid(M) &&
      store_type(M, t1, tr1) && store_type(M, t2, tr2) &&
      repr_rel_node(s, tr1, tr1) && rc_capacity(1, M, s, t1, t2) &&
      store_world(M) * store_solution(M, res, s)
    Ensure
      (exists M_post s_post,
        __return == 0 &&
        unify_rel(tr1, tr2, s, s_post) &&
        infer_result(1, M, s, t1, t2, __return, M_post, s_post) &&
        rc_valid(M_post) && rc_preserves(M, M_post) &&
        rc_reservations_same(M, M_post) &&
        store_world(M_post) * store_solution(M_post, res, s_post))
      ||
      (exists M_post s_post,
        __return != 0 &&
        infer_result(1, M, s, t1, t2, __return, M_post, s_post) &&
        rc_valid(M_post) && rc_preserves(M, M_post) &&
        rc_reservations_same(M, M_post) &&
        store_world(M_post) * store_solution(M_post, res, s_post))
*/
;

int atype_unify2(struct atype *t1, struct atype *t2)
/*@ With (M : RcState) (s : sol) (tr1 : TypeTree) (tr2 : TypeTree)
    Require rc_valid(M) &&
      store_type(M, t1, tr1) && store_type(M, t2, tr2) &&
      repr_rel_node(s, tr1, tr1) && repr_rel_node(s, tr2, tr2) &&
      rc_capacity(2, M, s, t1, t2) && store_world(M) * store_solution(M, res, s)
    Ensure
      (exists M_post s_post,
        __return == 0 &&
        unify_rel(tr1, tr2, s, s_post) &&
        infer_result(2, M, s, t1, t2, __return, M_post, s_post) &&
        rc_valid(M_post) && rc_preserves(M, M_post) &&
        rc_reservations_same(M, M_post) &&
        store_world(M_post) * store_solution(M_post, res, s_post))
      ||
      (exists M_post s_post,
        __return != 0 &&
        infer_result(2, M, s, t1, t2, __return, M_post, s_post) &&
        rc_valid(M_post) && rc_preserves(M, M_post) &&
        rc_reservations_same(M, M_post) &&
        store_world(M_post) * store_solution(M_post, res, s_post))
*/
;

int atype_unify(struct atype *t1, struct atype *t2)
/*@ final <= verify
    With (M : RcState) (s_pre : sol) (raw : sol) (tr1 : TypeTree) (tr2 : TypeTree)
    Require 
        rc_valid(M) && store_type(M, t1, tr1) && store_type(M, t2, tr2) &&
        sol_compress_to(raw, s_pre) && sol_finite(s_pre) && sol_no_loop(raw) &&
        rc_capacity(0, M, raw, t1, t2) &&
        store_world(M) * store_solution(M, res, raw)
    Ensure
        (
            (
            exists s_post M_post,
                __return == 0 &&
                sol_correct_iter(tr1, tr2, s_pre, s_post) &&
                rc_valid(M_post) && rc_preserves(M, M_post) &&
                store_type(M_post, t1, tr1) && store_type(M_post, t2, tr2) &&
                store_world(M_post) * store_compressed_solution(M_post, res, s_post)
            )
            ||
            (
            exists s_post M_post,
                __return != 0 &&
                rc_valid(M_post) && rc_preserves(M, M_post) &&
                store_type(M_post, t1, tr1) && store_type(M_post, t2, tr2) &&
                store_world(M_post) * store_solution(M_post, res, s_post)
            )
        )
*/;

int atype_unify(struct atype *t1, struct atype *t2)
/*@ verify With (M : RcState) (s : sol) (tr1 : TypeTree) (tr2 : TypeTree)
    Require rc_valid(M) &&
      store_type(M, t1, tr1) && store_type(M, t2, tr2) &&
      rc_capacity(0, M, s, t1, t2) && store_world(M) * store_solution(M, res, s)
    Ensure
      (exists M_post s_post,
        __return == 0 &&
        unify_rel(tr1, tr2, s, s_post) &&
        infer_result(0, M, s, t1, t2, __return, M_post, s_post) &&
        rc_valid(M_post) && rc_preserves(M, M_post) &&
        rc_reservations_same(M, M_post) &&
        store_world(M_post) * store_solution(M_post, res, s_post))
      ||
      (exists M_post s_post,
        __return != 0 &&
        infer_result(0, M, s, t1, t2, __return, M_post, s_post) &&
        rc_valid(M_post) && rc_preserves(M, M_post) &&
        rc_reservations_same(M, M_post) &&
        store_world(M_post) * store_solution(M_post, res, s_post))
*/
{
  if (t1 -> t == AT_VAR) {
    struct atype *tp = get_map(t1 -> d.VAR.name);
    if (tp) {
      
      t1 = atype_repr(t1 -> d.VAR.name);
      /* The call-post strategies already transport the untouched t2 facts. */
      int r = atype_unify1(t1, t2) /*@ where tr2 = tr2 */;
      free_atype(t1) /*@ where(nonnull) */;
      return r;
    } else {
      return atype_unify1(t1, t2) /*@ where tr1 = tr1, tr2 = tr2 */;
    }
  } else {
    return atype_unify1(t1, t2) /*@ where M = M, s = s, tr1 = tr1, tr2 = tr2 */;
  }
}

int atype_unify1(struct atype *t1, struct atype *t2)
/*@ default */
{
  if (t2 -> t == AT_VAR) {
    struct atype *tp = get_map(t2 -> d.VAR.name);
    if (tp) {
      
      t2 = atype_repr(t2 -> d.VAR.name);
      /* The call-post strategies already transport the untouched t1 facts. */
      int r = atype_unify2(t1, t2) /*@ where tr1 = tr1 */;
      free_atype(t2) /*@ where(nonnull) */;
      return r;
    } else {
      return atype_unify2(t1, t2) /*@ where tr1 = tr1, tr2 = tr2 */;
    }
  } else {
    return atype_unify2(t1, t2) /*@ where M = M, s = s, tr1 = tr1, tr2 = tr2 */;
  }
}

int atype_unify2(struct atype *t1, struct atype *t2)
/*@ default */
{
  /*@ Destruct with
        same_node: t1 == t2;
        distinct_nodes: t1 != t2
  */
  if (t1->t == AT_VAR)
  {
    int occur = type_var_occur(t1->d.VAR.name, t2) /*@ where p = t1, tr = tr2 */;
    if (occur)
    {
      return 1;
    }
    else
    {
      add_map(t1->d.VAR.name, copy_atype(t2) /*@ where(open_var) p = t1 */) /*@ where p = t1, tr = tr2 */;
      return 0;
    }
  }

  if (t2->t == AT_VAR)
  {
    int occur = type_var_occur(t2->d.VAR.name, t1) /*@ where p = t2, tr = tr1 */;
    if (occur)
    {
      return 1;
    }
    else
    {
      add_map(t2->d.VAR.name, copy_atype(t1) /*@ where(open_var) p = t2 */) /*@ where p = t2, tr = tr1 */;
      return 0;
    }
  }

  if (t1->t != t2->t)
  {
    return 2;
  }

  if (t1->t == AT_ARROW)
  {
    struct atype *arrow_from1 = t1->d.ARROW.from;
    struct atype *arrow_from2 = t2->d.ARROW.from;
    int r = atype_unify(arrow_from1, arrow_from2) /*@ where(verify) */;
    if (r != 0)
    {
      return r;
    }
    struct atype *arrow_to1 = t1->d.ARROW.to;
    struct atype *arrow_to2 = t2->d.ARROW.to;
    return atype_unify(arrow_to1, arrow_to2) /*@ where(verify) */;
  }

  if (t1->t == AT_APP)
  {
    struct atype *app_tfn1 = t1->d.APP.tfn;
    struct atype *app_tfn2 = t2->d.APP.tfn;
    int r = atype_unify(app_tfn1, app_tfn2) /*@ where(verify) */;
    if (r != 0)
    {
      return r;
    }
    struct atype *app_rand1 = t1->d.APP.rand;
    struct atype *app_rand2 = t2->d.APP.rand;
    return atype_unify(app_rand1, app_rand2) /*@ where(verify) */;
  }

  if (t1->d.ATOM.name == t2->d.ATOM.name)
  {
    return 0;
  }
  else
  {
    return 2;
  }
}

