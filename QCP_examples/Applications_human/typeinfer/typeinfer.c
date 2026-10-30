#include "tool.h"

struct atype *res[100];

struct atype *get_map(int n)
/*@ With (s : sol)
    Require
      0 <= n && n < 100 &&
      store_solution(res, s)
    Ensure
      exists tr,
        store_solution_aux(res, s, n, __return, tr)
*/;

void add_map(int n, struct atype *t)
/*@ With (s : sol) (tr : TypeTree)
    Require
      0 <= n && n < 100 && not_occur_final(s, n, tr) &&
      store_type(t, tr) *
      store_solution(res, s)
    Ensure
      exists s_post,
        sol_update(s, n, tr) == s_post &&
        store_solution(res, s_post)
*/
;

struct atype *copy_atype(struct atype *t)
/*@ With (tr : TypeTree)
    Require store_type(t, tr)
    Ensure store_type(t, tr) * store_type(__return, tr)
*/
;

void free_atype(struct atype *t)
/*@ With (tr : TypeTree)
    Require store_type(t, tr)
    Ensure emp
*/
;

int type_var_occur(int v, struct atype *t)
/*@ With (s : sol) (tr : TypeTree)
    Require
        0 <= v && v < 100 &&
        store_type(t, tr) *
        store_solution(res, s)
    Ensure
      (
        __return != 0 &&
        store_type(t, tr) *
        store_solution(res, s)
      )
      ||
      (
        __return == 0 &&
        not_occur_final(s, v, tr) &&
        store_type(t, tr) *
        store_solution(res, s)
      )
*/
;

struct atype *atype_repr(int n)
/*@ With (s : sol) (tr : TypeTree)
    Require
        0 <= n && n < 100 &&
        solution_at(s, n, tr) &&
        store_solution(res, s)

    Ensure
        exists tr_repr,
            store_type(__return, tr_repr) &&
            repr_rel_node(s, TVar(n), tr_repr) &&
            store_solution(res, s)
*/
;

int atype_unify1(struct atype *t1, struct atype *t2)
/*@ With (s_pre : sol) (tr1 : TypeTree) (tr2 : TypeTree)
    (tr1_prev : TypeTree)
    Require
        repr_rel_node(s_pre, tr1_prev, tr1) &&
        store_solution(res, s_pre) *
        store_type(t1, tr1) *
        store_type(t2, tr2)

    Ensure
        (
            (
            exists s_post,
                __return == 0 &&
                unify_rel(tr1_prev, tr2, s_pre, s_post) &&
                store_solution(res, s_post) *
                store_type(t1, tr1) *
                store_type(t2, tr2)
            )
            ||
            (
            exists s_post,
                __return != 0 &&
                store_solution(res, s_post) *
                store_type(t1, tr1) *
                store_type(t2, tr2)
            )
        )
*/
;

int atype_unify2(struct atype *t1, struct atype *t2)
/*@ With (s_pre : sol) (tr1 : TypeTree) (tr2 : TypeTree)
    (tr1_prev : TypeTree) (tr2_prev : TypeTree)
    Require
        repr_rel_node(s_pre, tr1_prev, tr1) &&
        repr_rel_node(s_pre, tr2_prev, tr2) &&
        store_solution(res, s_pre) *
        store_type(t1, tr1) *
        store_type(t2, tr2)

    Ensure
        (
            (
            exists s_post,
                __return == 0 &&
                unify_rel(tr1_prev, tr2_prev, s_pre, s_post) &&
                store_solution(res, s_post) *
                store_type(t1, tr1) *
                store_type(t2, tr2)
            )
            ||
            (
            exists s_post,
                __return != 0 &&
                store_solution(res, s_post) *
                store_type(t1, tr1) *
                store_type(t2, tr2)
            )
        )
*/
;

int atype_unify(struct atype *t1, struct atype *t2)
/*@ final <= verify
    With (s_pre : sol) (tr1 : TypeTree) (tr2 : TypeTree)
    Require 
        store_compressed_solution(res, s_pre) *
        store_type(t1, tr1) *
        store_type(t2, tr2)
    Ensure
        (
            (
            exists s_post,
                __return == 0 &&
                sol_correct_iter(tr1, tr2, s_pre, s_post) &&
                store_compressed_solution(res, s_post) *
                store_type(t1, tr1) *
                store_type(t2, tr2)
            )
            ||
            (
            exists s_post,
                __return != 0 &&
                store_solution(res, s_post) *
                store_type(t1, tr1) *
                store_type(t2, tr2)
            )
        )
*/;


int atype_unify(struct atype *t1, struct atype *t2)
/*@ verify
    With (s_pre : sol) (tr1 : TypeTree) (tr2 : TypeTree)
    Require
        store_solution(res, s_pre) *
        store_type(t1, tr1) *
        store_type(t2, tr2)
    Ensure
        (
            (
            exists s_post,
                __return == 0 &&
                unify_rel(tr1, tr2, s_pre, s_post) &&
                store_solution(res, s_post) *
                store_type(t1, tr1) *
                store_type(t2, tr2)
            )
            ||
            (
            exists s_post,
                __return != 0 &&
                store_solution(res, s_post) *
                store_type(t1, tr1) *
                store_type(t2, tr2)
            )
        )
*/
{
  /*@ store_type(t1, tr1)
        which implies
      store_type_aux(t1, t1 -> t, tr1) */
  if (t1 -> t == AT_VAR) {
    /*@ t1 -> t == AT_VAR &&
        store_type_aux(t1, t1 -> t, tr1)

          which implies

        exists n,
          t1 -> t == AT_VAR &&
          t1 -> d.VAR.name == n &&
          0 <= n && n < 100 &&
          tr1 == TVar(n)
    */
    struct atype *tp = get_map(t1 -> d.VAR.name);
    if (tp) {
      /*@ exists tr_opt n,
            t1 -> d.VAR.name == n &&
            tp != 0 && 0 <= n && n < 100 &&
            store_solution_aux(res, s_pre, n, tp, tr_opt)

              which implies

          exists tr,
            tp == tp &&
            t1 -> d.VAR.name == n &&
            tr_opt == Some(tr) &&
            solution_at(s_pre, n, tr) &&
            store_solution(res, s_pre)
      */
      t1 = atype_repr(t1 -> d.VAR.name);
      int r = atype_unify1(t1, t2);
      free_atype(t1);
      return r;
    } else {
      /*@ exists tr_opt n,
            tp == 0 &&
            t1 -> t == AT_VAR &&
            t1 -> d.VAR.name == n &&
            0 <= n && n < 100 &&
            tr1 == TVar(n) &&
            store_solution_aux(res, s_pre, t1 -> d.VAR.name, tp, tr_opt)

              which implies

          tp == tp &&
          tr_opt == None &&
          repr_rel_node(s_pre, tr1, tr1) &&
          store_solution(res, s_pre) *
          store_type(t1, tr1)
      */
      return atype_unify1(t1, t2);
    }
  } else {
    /*@ t1 -> t != AT_VAR &&
        store_type_aux(t1, t1 -> t, tr1) *
        store_solution(res, s_pre)

            which implies

        repr_rel_node(s_pre, tr1, tr1) &&
        store_type(t1, tr1) *
        store_solution(res, s_pre)
    */
    return atype_unify1(t1, t2);
  }
}

int atype_unify1(struct atype *t1, struct atype *t2)
/*@ default */
{
  /*@ store_type(t2, tr2)
        which implies
      store_type_aux(t2, t2 -> t, tr2) */
  if (t2 -> t == AT_VAR) {
    /*@ t2 -> t == AT_VAR &&
        store_type_aux(t2, t2 -> t, tr2)

          which implies

        exists n,
          t2 -> t == AT_VAR &&
          t2 -> d.VAR.name == n &&
          0 <= n && n < 100 &&
          tr2 == TVar(n)
    */
    struct atype *tp = get_map(t2 -> d.VAR.name);
    if (tp) {
      /*@ exists tr_opt n,
            t2 -> d.VAR.name == n &&
            tp != 0 && 0 <= n && n < 100 &&
            store_solution_aux(res, s_pre, n, tp, tr_opt)

              which implies

          exists tr,
            tp == tp &&
            t2 -> d.VAR.name == n &&
            tr_opt == Some(tr) &&
            solution_at(s_pre, n, tr) &&
            store_solution(res, s_pre)
      */
      t2 = atype_repr(t2 -> d.VAR.name);
      int r = atype_unify2(t1, t2);
      free_atype(t2);
      return r;
    } else {
      /*@ exists tr_opt n,
            tp == 0 &&
            t2 -> t == AT_VAR &&
            t2 -> d.VAR.name == n &&
            0 <= n && n < 100 &&
            tr2 == TVar(n) &&
            store_solution_aux(res, s_pre, t2 -> d.VAR.name, tp, tr_opt)

              which implies

          tp == tp &&
          tr_opt == None &&
          repr_rel_node(s_pre, tr2, tr2) &&
          store_solution(res, s_pre) *
          store_type(t2, tr2)
      */
      return atype_unify2(t1, t2);
    }
  } else {
    /*@ t2 -> t != AT_VAR &&
        store_type_aux(t2, t2 -> t, tr2) *
        store_solution(res, s_pre)

            which implies

        repr_rel_node(s_pre, tr2, tr2) &&
        store_type(t2, tr2) *
        store_solution(res, s_pre)
    */
    return atype_unify2(t1, t2);
  }
}


int atype_unify2(struct atype *t1, struct atype *t2)
/*@ default */
{
  /*@ store_type(t1, tr1)
        which implies
      store_type_aux(t1, t1 -> t, tr1) */
  if (t1->t == AT_VAR)
  {
    /*@ t1 -> t == AT_VAR &&
        store_type_aux(t1, t1 -> t, tr1)

          which implies

        exists n,
          t1 -> t == AT_VAR &&
          t1 -> d.VAR.name == n &&
          0 <= n && n < 100 &&
          tr1 == TVar(n)
    */
    int occur = type_var_occur(t1->d.VAR.name, t2);
    if (occur)
    {
      return 1;
    }
    else
    {
      add_map(t1->d.VAR.name, copy_atype(t2));
      return 0;
    }
  }

  /*@ store_type(t2, tr2)
        which implies
      store_type_aux(t2, t2 -> t, tr2) */

  if (t2->t == AT_VAR)
  {
    /*@ t2 -> t == AT_VAR &&
        store_type_aux(t2, t2 -> t, tr2)

            which implies

        exists n,
          t2 -> t == AT_VAR &&
          t2 -> d.VAR.name == n &&
          0 <= n && n < 100 &&
          tr2 == TVar(n)
    */

    /*@ store_type_aux(t1, t1 -> t, tr1)
          which implies
        store_type(t1, tr1)
    */

    int occur = type_var_occur(t2->d.VAR.name, t1);
    if (occur)
    {
      return 1;
    }
    else
    {
      add_map(t2->d.VAR.name, copy_atype(t1));
      return 0;
    }
  }


  if (t1->t != t2->t)
  {
    return 2;
  }


  if (t1->t == AT_ARROW)
  {
    /*@ t1 -> t == AT_ARROW &&
        t1 -> t == t2 -> t &&
        store_type_aux(t1, t1 -> t, tr1) &&
        store_type_aux(t2, t2 -> t, tr2)

          which implies

        exists tr1_from tr1_to tr2_from tr2_to
          t1_from t1_to t2_from t2_to,
          t1 -> d.ARROW.from == t1_from &&
          store_type(t1_from, tr1_from) &&
          t1 -> d.ARROW.to == t1_to &&
          store_type(t1_to, tr1_to) &&
          tr1 == TArrow(tr1_from, tr1_to) &&

          t2 -> d.ARROW.from == t2_from &&
          store_type(t2_from, tr2_from) &&
          t2 -> d.ARROW.to == t2_to &&
          store_type(t2_to, tr2_to) &&
          tr2 == TArrow(tr2_from, tr2_to) &&

          t1 -> t == AT_ARROW &&
          t2 -> t == AT_ARROW
    */
    int r = atype_unify(t1->d.ARROW.from, t2->d.ARROW.from);
    if (r != 0)
    {
      return r;
    }
    return atype_unify(t1->d.ARROW.to, t2->d.ARROW.to);
  }

  if (t1->t == AT_APP)
  {
    /*@ t1 -> t == AT_APP &&
        t1 -> t == t2 -> t &&
        store_type_aux(t1, t1 -> t, tr1) &&
        store_type_aux(t2, t2 -> t, tr2)

          which implies

        exists tr1_tfn tr1_rand tr2_tfn tr2_rand
          t1_tfn t1_rand t2_tfn t2_rand,
          t1 -> d.APP.tfn == t1_tfn &&
          store_type(t1_tfn, tr1_tfn) &&
          t1 -> d.APP.rand == t1_rand &&
          store_type(t1_rand, tr1_rand) &&
          tr1 == TApply(tr1_tfn, tr1_rand) &&

          t2 -> d.APP.tfn == t2_tfn &&
          store_type(t2_tfn, tr2_tfn) &&
          t2 -> d.APP.rand == t2_rand &&
          store_type(t2_rand, tr2_rand) &&
          tr2 == TApply(tr2_tfn, tr2_rand) &&

          t1 -> t == AT_APP &&
          t2 -> t == AT_APP
    */
    int r = atype_unify(t1->d.APP.tfn, t2->d.APP.tfn);
    if (r != 0)
    {
      return r;
    }
    return atype_unify(t1->d.APP.rand, t2->d.APP.rand);
  }

  /*@ store_type_aux(t1, t1 -> t, tr1) &&
      store_type_aux(t2, t2 -> t, tr2) &&
      t1 -> t == t2 -> t &&
      t1 -> t != AT_VAR &&
      t1 -> t != AT_ARROW &&
      t1 -> t != AT_APP

          which implies

      exists n m,
          t1 -> t == AT_ATOM &&
          t2 -> t == AT_ATOM &&
          t1 -> d.ATOM.name == n &&
          t2 -> d.ATOM.name == m &&
          tr1 == TAtom(n) &&
          tr2 == TAtom(m)
  */

  if (t1->d.ATOM.name == t2->d.ATOM.name)
  {
    return 0;
  }
  else
  {
    return 2;
  }
}
