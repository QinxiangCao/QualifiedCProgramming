#include "typeinfer_rc.h"
/*@ Import Coq Require Import SimpleC.EE.Applications_human.typeinfer_rc.typeinfer_rc_lib */
/*@ include strategies "typeinfer_rc.strategies" */

struct atype *res[100];

/* Exactly the existing verification contract, with only the local spec name
   omitted. The diagnostic callers never request a post-state type or node. */
int atype_unify(struct atype *t1, struct atype *t2)
/*@ With (M : RcState) (s : sol) (tr1 : TypeTree) (tr2 : TypeTree)
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
*/;

void third_variable(struct atype *t1, struct atype *t2, struct atype *p)
/*@ With (M : RcState) (s : sol) (tr1 : TypeTree) (tr2 : TypeTree)
         (tr : TypeTree) (n : TypeNode)
    Require rc_valid(M) && store_type(M, t1, tr1) && store_type(M, t2, tr2) &&
      store_type(M, p, tr) && node_at(M, p, n) &&
      rc_capacity(0, M, s, t1, t2) && store_world(M) * store_solution(M, res, s)
    Ensure exists N sn, store_world(N) * store_solution(N, res, sn)
*/
{
  atype_unify(t1, t2);
}

void alias_variable(struct atype *t1, struct atype *t2, struct atype *p)
/*@ With (M : RcState) (s : sol) (tr1 : TypeTree) (tr2 : TypeTree)
         (tr : TypeTree) (n : TypeNode)
    Require p == t1 && t1 == t2 && rc_valid(M) &&
      store_type(M, t1, tr1) && store_type(M, t2, tr2) &&
      store_type(M, p, tr) && node_at(M, p, n) &&
      rc_capacity(0, M, s, t1, t2) && store_world(M) * store_solution(M, res, s)
    Ensure exists N sn, store_world(N) * store_solution(N, res, sn)
*/
{
  atype_unify(t1, t2);
}

/* Small abstract boundaries isolate post-processing from unification details. */
void preserving_step(void)
/*@ With (M : RcState)
    Require store_world(M)
    Ensure exists N, rc_preserves(M, N) && store_world(N)
*/;

void masked_step(void)
/*@ With (M : RcState) (L : list TypeFieldKey)
    Require store_world_missing(M, L)
    Ensure exists N, rc_preserves(M, N) && store_world_missing(N, L)
*/;

void unchanged_step(void)
/*@ With (M : RcState)
    Require store_world(M)
    Ensure rc_preserves(M, M) && store_world(M)
*/;

void unpromised_step(void)
/*@ With (M : RcState)
    Require store_world(M)
    Ensure exists N, store_world(N)
*/;

void chained_calls(struct atype *p)
/*@ With (M : RcState) (tr : TypeTree) (n : TypeNode)
    Require store_type(M, p, tr) && node_at(M, p, n) && store_world(M)
    Ensure exists N, store_world(N)
*/
{
  preserving_step();
  preserving_step();
  preserving_step();
}

void partial_world(struct atype *p)
/*@ With (M : RcState) (tr : TypeTree) (n : TypeNode) (L : list TypeFieldKey)
    Require store_type(M, p, tr) && node_at(M, p, n) && store_world_missing(M, L)
    Ensure exists N, store_world_missing(N, L)
*/
{
  masked_step();
  masked_step();
}

void reflexive_calls(struct atype *p)
/*@ With (M : RcState) (tr : TypeTree) (n : TypeNode)
    Require store_type(M, p, tr) && node_at(M, p, n) && store_world(M)
    Ensure store_world(M)
*/
{
  unchanged_step();
  unchanged_step();
}

void no_preserves(struct atype *p)
/*@ With (M : RcState) (tr : TypeTree) (n : TypeNode)
    Require store_type(M, p, tr) && node_at(M, p, n) && store_world(M)
    Ensure exists N, store_world(N)
*/
{
  unpromised_step();
}

void stale_history(struct atype *p)
/*@ With (M : RcState) (H : RcState) (tr : TypeTree) (n : TypeNode)
    Require store_type(M, p, tr) && node_at(M, p, n) &&
      rc_preserves(M, H) && store_world(M)
    Ensure exists N, store_world(N)
*/
{
  preserving_step();
}

void cyclic_history(struct atype *p)
/*@ With (M : RcState) (H : RcState) (tr : TypeTree) (n : TypeNode)
    Require store_type(M, p, tr) && node_at(M, p, n) &&
      rc_preserves(M, H) && rc_preserves(H, M) && store_world(M)
    Ensure store_world(M)
*/
{
  unchanged_step();
  unchanged_step();
}

void already_present(struct atype *p)
/*@ With (M : RcState) (H : RcState) (tr : TypeTree) (n : TypeNode)
    Require store_type(H, p, tr) && node_at(H, p, n) &&
      store_type(M, p, tr) && node_at(M, p, n) &&
      rc_preserves(H, M) && store_world(M)
    Ensure store_world(M)
*/
{
  unchanged_step();
}
