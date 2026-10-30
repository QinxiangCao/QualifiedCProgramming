

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

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.sll_merge_rel_lib */

struct list *merge(struct list *x, struct list *y)
/*@ With s1 s2 X
    Require safeExec(ATrue, merge_rel(s1, s2), X) && sll(x, s1) * sll(y, s2)
    Ensure exists s3, safeExec(ATrue, return(s3), X) && sll(__return, s3)
*/
{
  struct list **t, *ret;
  t = &ret;
  /*@ Inv
    exists l1 l2 l3,
      safeExec(ATrue, merge_from_mid_rel(l1, l2, l3), X) && 
      sll(x, l1) * sll(y, l2) *
      undef_data_at(t, struct list*) * sllbseg(&ret, t, l3)
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
    /*@ exists l1, x != 0 && sll(x, l1)
        which implies 
        exists l1_new, l1 == cons(x->data, l1_new) && sll(x->next, l1_new)
    */
    /*@ exists l2, y != 0 && sll(y, l2)
        which implies 
        exists l2_new, l2 == cons(y->data, l2_new) && sll(y->next, l2_new)
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
  /*@
    exists l3 u, store(t, struct list*, u) * sllbseg(&ret, t, l3)
    which implies
    t == t && sllseg(ret, u, l3)
  */
  return ret;
}

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ high_level_spec <= low_level_spec
      With l X
      Require safeExec(ATrue, split_rel(l), X) &&
              sll(x, l) * sll(* p, nil) * sll(* q, nil)
      Ensure exists s1 s2,
              safeExec(ATrue, return(maketuple(s1, s2)), X) && 
              sll(* p, s1) * sll(* q, s2)
   */
;

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} l l1 l2 (c : ((list Z) * (list Z)) -> program unit B) X
      Require safeExec(ATrue, bind(split_rec_rel(l, l1, l2), c), X) &&
              sll(x, l) * sll(* p, l1) * sll(* q, l2)
      Ensure exists s1 s2,
              safeExec(ATrue, applyf(c, maketuple(s1,s2)), X) &&
              sll(* p, s1) * sll(* q, s2)
   */
;

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ low_level_spec
      With l l1 l2 X
      Require safeExec(ATrue, split_rec_rel(l, l1, l2), X) &&
              sll(x, l) * sll(* p, l1) * sll(* q, l2)
      Ensure exists s1 s2,
              safeExec(ATrue, return(maketuple(s1, s2)), X) &&
              sll(* p, s1) * sll(* q, s2)
  */
{
  if (x == (void *)0) {
    return;
  }
  /*@ exists l, x != 0 && sll(x, l)
      which implies
      exists l_new, l == cons(x->data, l_new) && sll(x->next, l_new)
  */
  struct list * t;
  t = x -> next;
  x -> next = * p;
  * p = x;
  /*@ exists l_new x_data, 
        safeExec(ATrue, split_rec_rel(l, l1, l2), X) && l == cons(x_data, l_new) &&
        (* p) != 0 && (* p) -> data == x_data && sll((* p) -> next, l1) * sll(t,l_new)
      which implies
      safeExec(ATrue, bind(split_rec_rel(l_new, l2, cons(x_data, l1)), reversepair) , X) && sll(* p, cons(x_data, l1)) * sll(t,l_new)
  */
  split_rec(t, q, p) /*@ where(low_level_spec_aux) {B = (list Z) * (list Z)} l1 = l2, c = reversepair,  X = X */;
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
  /*@ p == 0 && emp
      which implies
      sll(p, nil) */
  q = (void *)0;
  /*@ q == 0 && emp
      which implies
      sll(q, nil) */
  /*@ safeExec(ATrue, bind(split_rel(l), mergesortrec_loc0), X) && emp */
  split_rec(x, &p, &q) /*@ where(low_level_spec_aux) {B = (list Z)} X = X, c = mergesortrec_loc0 */;
  if (q == (void *)0) {
    return p;
  }
  /*@ exists l1 l2, safeExec(ATrue, bind(mergesortrec(l1), mergesortrec_loc1(l2)), X) && sll(p, l1) * sll(q, l2)  */
  p = merge_sort(p) /*@ where(low_level_spec_aux) {B = (list Z)} X = X */;
  /*@ exists l1 l2, safeExec(ATrue, bind(mergesortrec(l2), mergesortrec_loc2(l1)), X) && sll(p, l1) * sll(q, l2)  */
  q = merge_sort(q) /*@ where(low_level_spec_aux) {B = (list Z)} X = X */;
  /*@ exists l1 l2, safeExec(ATrue, merge_rel(l1, l2), X) && sll(p, l1) * sll(q, l2) */
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
  /*@ p == 0 && emp
      which implies
      sll(p, nil) */
  q = (void *)0;
  /*@ q == 0 && emp
      which implies
      sll(q, nil) */
  /*@ safeExec(ATrue, bind(split_rel(l), gmergesortrec_loc0), X) && emp */
  split_rec(x, &p, &q) /*@ where(low_level_spec_aux) {B = (list Z)} X = X, c = gmergesortrec_loc0 */;
  /*@ exists l1 l2, safeExec(ATrue, bind(gmergesortrec(l1), gmergesortrec_loc1(l2)), X) && sll(p, l1) * sll(q, l2) */
  p = merge_sort2(p) /*@ where(low_level_spec_aux) {B = (list Z)} X = X */;
  /*@ exists l1 l2, safeExec(ATrue, bind(gmergesortrec(l2), mergesortrec_loc2(l1)), X) && sll(p, l1) * sll(q, l2) */
  q = merge_sort2(q) /*@ where(low_level_spec_aux) {B = (list Z)} X = X */;
  /*@ exists l1 l2, safeExec(ATrue, merge_rel(l1, l2), X) && sll(p, l1) * sll(q, l2) */
  return merge(p, q) /*@ where X = X */;
}

