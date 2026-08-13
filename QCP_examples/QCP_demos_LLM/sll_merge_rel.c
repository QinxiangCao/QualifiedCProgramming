

#include "sll_def.h"
#include "safeexec_def.h"

/*@ Extern Coq 
               (maketuple: list Z -> list Z ->  ((list Z) * (list Z)))
               (merge_rel: list Z -> list Z -> program unit (list Z))
               (merge_from_mid_rel: list Z -> list Z -> list Z -> program unit (list Z))
               (split_rec_rel: list Z -> list Z -> list Z -> program unit ((list Z) * (list Z)))
               (split_rel: list Z -> program unit ((list Z) * (list Z)))
               (reversepair: ((list Z) * (list Z)) -> program unit ((list Z) * (list Z)))
               (mergesortrec: list Z -> program unit (list Z))
               (mergesortrec_loc1: list Z -> list Z -> program unit (list Z))
               (mergesortrec_loc2: list Z -> list Z -> program unit (list Z))
               (gmergesortrec: list Z -> program unit (list Z))
               (mergesortrec_loc0: ((list Z) * (list Z)) -> program unit (list Z))
               (gmergesortrec_loc0: ((list Z) * (list Z)) -> program unit (list Z))
               (gmergesortrec_loc1: list Z -> list Z -> program unit (list Z))
               (Permutation: list Z -> list Z -> Prop)
               (incr: list Z -> Prop)
                */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib */

struct list *merge(struct list *x, struct list *y)
/*@ With s1 s2 X
    Require safeExec(ATrue, merge_rel(s1, s2), X) && sll(x, s1) * sll(y, s2)
    Ensure exists s3, safeExec(ATrue, return(s3), X) && sll(__return, s3)
*/
{
  struct list **t, *ret;
  t = &ret;
  /*@ Inv Assert
    exists l1 l2 l3,
      safeExec(ATrue, merge_from_mid_rel(l1, l2, l3), X) && 
      sll(x, l1) * sll(y, l2) *
      has_ptr_permission(t) * sllbseg(&ret, t, l3)
  */
  while (1)
  {
    if (x == (void *)0) {
      *t = y;
      break;
    }
    if (y == (void *)0) {
      *t = x;
      break;
    }
    /*@ Assert
      exists l1 l2 l3 l1_new l2_new xdata ydata xnext ynext,
        safeExec(ATrue, merge_from_mid_rel(l1, l2, l3), X) &&
        x != 0 && y != 0 &&
        l1 == cons(xdata, l1_new) &&
        l2 == cons(ydata, l2_new) &&
        store(&(x->data), xdata) * store(&(y->data), ydata) *
        store(&(x->next), xnext) * store(&(y->next), ynext) *
        sll(xnext, l1_new) * sll(ynext, l2_new) *
        has_ptr_permission(t) * sllbseg(&ret, t, l3)
    */
    if (x->data < y->data) {
      *t = x;
      t = &(x->next);
      x = x->next;
    } else {
      *t = y;
      t = &(y->next);
      y = y->next;
    }
  }
  /*@ Assert
      exists s3,
        safeExec(ATrue, return(s3), X) &&
        store(&x, struct list*, x) *
        store(&y, struct list*, y) *
        store(&t, struct list**, t) *
        sll(ret, s3)
  */
  return ret;
}

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ high_level_spec <= low_level_spec
      With l X pv qv
      Require safeExec(ATrue, split_rel(l), X) &&
              store(p, pv) * store(q, qv) *
              sll(x, l) * sll(pv, nil) * sll(qv, nil)
      Ensure exists s1 s2 pv' qv',
              safeExec(ATrue, return(maketuple(s1, s2)), X) &&
              store(p, pv') * store(q, qv') * 
              sll(pv', s1) * sll(qv', s2)
   */
;

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} l l1 l2 (c : ((list Z) * (list Z)) -> program unit B) X pv qv
      Require safeExec(ATrue, bind(split_rec_rel(l, l1, l2), c), X) &&
              store(p, pv) * store(q, qv) *
              sll(x, l) * sll(pv, l1) * sll(qv, l2)
      Ensure exists s1 s2 pv' qv',
              safeExec(ATrue, applyf(c, maketuple(s1,s2)), X) &&
              store(p, pv') * store(q, qv') *
              sll(pv', s1) * sll(qv', s2)
   */
;

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ low_level_spec
      With l l1 l2 X pv qv
      Require safeExec(ATrue, split_rec_rel(l, l1, l2), X) &&
              store(p, pv) * store(q, qv) *
              sll(x, l) * sll(pv, l1) * sll(qv, l2)
      Ensure exists s1 s2 pv' qv',
              safeExec(ATrue, return(maketuple(s1, s2)), X) &&
              store(p, pv') * store(q, qv') *
              sll(pv', s1) * sll(qv', s2)
  */
{
  if (x == (void *)0) {
    return;
  }
  /*@ Assert
      exists l_new x_data x_next,
        x == x@pre && p == p@pre && q == q@pre &&
        x != 0 &&
        safeExec(ATrue, split_rec_rel(l, l1, l2), X) &&
        l == cons(x_data, l_new) &&
        store(&(x->data), x_data) * store(&(x->next), x_next) *
        store(p, pv) * store(q, qv) *
        sll(x_next, l_new) * sll(pv, l1) * sll(qv, l2)
  */
  struct list * t;
  t = x -> next;
  x -> next = * p;
  * p = x;
  /*@ Assert
      exists l_new x_data,
      x == x@pre && p == p@pre && q == q@pre &&
        x != 0 &&
        safeExec(ATrue, bind(split_rec_rel(l_new, l2, cons(x_data, l1)), reversepair), X) &&
        l == cons(x_data, l_new) &&
      store(p, x) * store(q, qv) *
      sll(x, cons(x_data, l1)) * sll(t, l_new) * sll(qv, l2)
  */
  split_rec(t, q, p) /*@ where(low_level_spec_aux) l1 = l2, c = reversepair,  X = X; B = (list Z) * (list Z) */; 
}

struct list * merge_sort(struct list * x)
  /*@ high_level_spec <= low_level_spec
      With l
      Require sll(x, l)
      Ensure exists l0,
              Permutation(l, l0) && incr(l0) &&
              sll(__return, l0)
   */
;

struct list * merge_sort(struct list * x)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} l (c: list Z -> program unit B) X
      Require safeExec(ATrue, bind(mergesortrec(l), c), X) && sll(x, l)
      Ensure exists l0,
              safeExec(ATrue, applyf(c, l0), X) && 
              sll(__return, l0)
   */
;

struct list * merge_sort(struct list * x)
  /*@ low_level_spec
      With l X
      Require safeExec(ATrue, mergesortrec(l), X) && sll(x, l)
      Ensure exists l0,
              safeExec(ATrue, return(l0), X) &&
              sll(__return, l0)
  */
{
  struct list * p, * q;
  p = (void *)0;
  /*@ Assert
    x == x@pre && p == 0 && has_ptr_permission(&q) && safeExec(ATrue, mergesortrec(l), X) && sll(p, nil) * sll(x, l)
  */
  q = (void *)0;
  /*@ Assert
    x == x@pre && p == 0 && q == 0 && safeExec(ATrue, mergesortrec(l), X) && sll(p, nil) * sll(q, nil) * sll(x, l)
  */
 /*@ Assert
    x == x@pre && p == 0 && q == 0 && safeExec(ATrue, bind(split_rel(l), mergesortrec_loc0), X) && sll(p, nil) * sll(q, nil) * sll(x, l)
  */
  split_rec(x, &p, &q) /*@ where(low_level_spec_aux) X = X, c = mergesortrec_loc0; B = (list Z) */;
  if (q == (void *)0) {
    return p;
  }
  /*@ Assert 
    exists l1 l2, 
    x == x@pre && q != 0 && 
    safeExec(ATrue, bind(mergesortrec(l1), mergesortrec_loc1(l2)), X) && sll(p, l1) * sll(q, l2)  */
  p = merge_sort(p) /*@ where(low_level_spec_aux) X = X; B = (list Z) */;
  /*@ Assert 
      exists l1 l2, 
      x == x@pre && q != 0 && 
      safeExec(ATrue, bind(mergesortrec(l2), mergesortrec_loc2(l1)), X) && sll(p, l1) * sll(q, l2)  */
  q = merge_sort(q) /*@ where(low_level_spec_aux) X = X; B = (list Z) */;
  /*@ Assert 
      exists l1 l2, x == x@pre && 
      safeExec(ATrue, merge_rel(l1, l2), X) && sll(p, l1) * sll(q, l2) */
  return merge(p, q) /*@ where X = X */;
}

struct list * insertion_sort(struct list * x)
  /*@ With l
      Require sll(x, l)
      Ensure exists l0,
              Permutation(l, l0) && incr(l0) &&
              sll(__return, l0)
   */
;

int length(struct list * x)
  /*@ With l
      Require sll(x, l) && Zlength(l) <= INT_MAX
      Ensure __return == Zlength(l) && sll(x,l)
   */
;

struct list * merge_sort2(struct list * x)
  /*@ high_level_spec <= low_level_spec
      With l
      Require sll(x, l)
      Ensure exists l0,
              Permutation(l, l0) && incr(l0) && 
              sll(__return, l0)
   */
;

struct list * merge_sort2(struct list * x)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} l (c: list Z -> program unit B) X
      Require safeExec(ATrue, bind(gmergesortrec(l), c), X) && sll(x, l)
      Ensure exists l0,
              safeExec(ATrue, applyf(c, l0), X) && 
              sll(__return, l0)
   */
;

struct list * merge_sort2(struct list * x)
  /*@ low_level_spec
      With l X
      Require safeExec(ATrue, gmergesortrec(l), X) && sll(x, l)
      Ensure exists l0,
              safeExec(ATrue, return(l0), X) && 
              sll(__return, l0)
  */
;

struct list * merge_sort3(struct list * x)
  /*@ high_level_spec <= low_level_spec
      With l
      Require Zlength(l) <= INT_MAX && sll(x, l)
      Ensure exists l0,
              Permutation(l, l0) && incr(l0) && 
              sll(__return, l0)
   */
;

struct list * merge_sort3(struct list * x)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} l (c: list Z -> program unit B) X
      Require Zlength(l) <= INT_MAX && safeExec(ATrue, bind(gmergesortrec(l), c), X) && sll(x, l)
      Ensure exists l0,
              safeExec(ATrue, applyf(c, l0), X) && 
              sll(__return, l0)
   */
;

struct list * merge_sort3(struct list * x)
  /*@ low_level_spec
      With l X
      Require Zlength(l) <= INT_MAX && safeExec(ATrue, gmergesortrec(l), X) && sll(x, l)
      Ensure exists l0,
              safeExec(ATrue, return(l0), X) && 
              sll(__return, l0)
  */
{
  struct list * p, * q;
  if (length(x) <= 8) {
    return insertion_sort(x);
  }
  p = (void *)0;
  /*@ Assert 
    x == x@pre && p == 0 && has_ptr_permission(&q) && 8 < Zlength(l) && Zlength(l) <= INT_MAX &&
    safeExec(ATrue, gmergesortrec(l), X) && sll(p, nil) * sll(x, l)
  */
  q = (void *)0;
  /*@ Assert
    x == x@pre && p == 0 && q == 0 && 8 < Zlength(l) && Zlength(l) <= INT_MAX &&
    safeExec(ATrue, gmergesortrec(l), X) && sll(p, nil) * sll(q, nil) * sll(x, l)
  */
  /*@ Assert 
    x == x@pre && p == 0 && q == 0 && 8 < Zlength(l) && Zlength(l) <= INT_MAX &&
      safeExec(ATrue, bind(split_rel(l), gmergesortrec_loc0), X) && sll(p, nil) * sll(q, nil) * sll(x, l)
  */
  split_rec(x, &p, &q) /*@ where(low_level_spec_aux) X = X, c = gmergesortrec_loc0; B = (list Z) */;
  /*@ Assert
    exists l1 l2, x == x@pre && 
    safeExec(ATrue, bind(gmergesortrec(l1), gmergesortrec_loc1(l2)), X) && sll(p, l1) * sll(q, l2)  */
  p = merge_sort2(p) /*@ where(low_level_spec_aux) X = X; B = (list Z) */;
  /*@ Assert 
      exists l1 l2, x == x@pre && 
      safeExec(ATrue, bind(gmergesortrec(l2), mergesortrec_loc2(l1)), X) && sll(p, l1) * sll(q, l2)
  */
  q = merge_sort2(q) /*@ where(low_level_spec_aux) X = X; B = (list Z) */;
  /*@ Assert 
       exists l1 l2, x == x@pre && 
       safeExec(ATrue, merge_rel(l1, l2), X) && sll(p, l1) * sll(q, l2)  */
  return merge(p, q) /*@ where X = X */;
}
