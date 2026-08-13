

#include "sll_def.h"
#include "safeexec_def.h"


/*@ Extern Coq (maketuple: list Z -> list Z ->  ((list Z) * (list Z)))
               (split_rec_rel: list Z -> list Z -> list Z -> program unit ((list Z) * (list Z)))
               (split_rel: list Z -> program unit ((list Z) * (list Z)))
               (reversepair: ((list Z) * (list Z)) -> program unit ((list Z) * (list Z)))
                */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib */

void split_while(struct list * x, struct list * * p, struct list * * q)
  /*@ low_level_spec
      With l X pv qv
      Require safeExec(ATrue, split_rec_rel(l, nil, nil), X) &&
              store(p, pv) * store(q, qv) *
              sll(x, l) * sll(pv, nil) * sll(qv, nil)
      Ensure exists s1 s2 pv' qv',
              safeExec(ATrue, return(maketuple(s1, s2)), X) &&
              store(p, pv') * store(q, qv') *
              sll(pv', s1) * sll(qv', s2)
  */
{

  struct list * t;


  /*@ Inv Assert
    exists l l1 l2 pv qv,
      p == p@pre && q == q@pre &&
      safeExec(ATrue, split_rec_rel(l, l1, l2), X) && 
      store(p, pv) * store(q, qv) *
      sll(x, l) * sll(pv, l1) * sll(qv, l2) *
      has_ptr_permission(&t)
  */
  while (x != (void *)0)
  {
    /*@ Assert
        exists l l1 l2 l1_new x_data x_next pv qv,
          p == p@pre && q == q@pre &&
          safeExec(ATrue, split_rec_rel(l, l1, l2), X) &&
          x != 0 &&
          l == cons(x_data, l1_new) &&
          store(&(x->data), x_data) * store(&(x->next), x_next) *
          store(p, pv) * store(q, qv) *
          sll(x_next, l1_new) * sll(pv, l1) * sll(qv, l2) *
          has_ptr_permission(&t)
    */
    t = x -> next;
    x -> next = * p;
    * p = x;
    x = t;
    /*@ Assert
        exists l l1 l2 l_new x_data p_head p_next qv,
          p == p@pre && q == q@pre &&
          safeExec(ATrue, bind(split_rec_rel(l_new, l2, cons(x_data, l1)), reversepair), X) &&
          l == cons(x_data, l_new) &&
          p_head != 0 &&
          store(p, p_head) * store(q, qv) *
          store(&(p_head->data), x_data) * store(&(p_head->next), p_next) *
          sll(p_next, l1) * sll(x, l_new) * sll(qv, l2) *
          has_ptr_permission(&t)
    */
    if (x != (void *)0)
    {
      /*@ Assert
          exists l l1 l2 l1_new x_data x_data2 x_next p_head qv,
            p == p@pre && q == q@pre &&
            safeExec(ATrue, bind(split_rec_rel(l, l2, cons(x_data, l1)), reversepair), X) &&
            x != 0 &&
            l == cons(x_data2, l1_new) &&
            store(&(x->data), x_data2) * store(&(x->next), x_next) *
            store(p, p_head) * store(q, qv) *
            sll(p_head, cons(x_data, l1)) * sll(qv, l2) * sll(x_next, l1_new) *
            has_ptr_permission(&t)
      */
      t = x -> next;
      x -> next = * q;
      * q = x;
      x = t;
      /*@ Assert
          exists l l1 l2 l_new x_data x_data2 p_head q_head q_next,
            p == p@pre && q == q@pre &&
            safeExec(ATrue, split_rec_rel(l_new, cons(x_data, l1), cons(x_data2, l2)), X) &&
            l == cons(x_data2, l_new) &&
            q_head != 0 &&
            store(p, p_head) * store(q, q_head) *
            store(&(q_head->data), x_data2) * store(&(q_head->next), q_next) *
            sll(q_next, l2) * sll(p_head, cons(x_data, l1)) * sll(x, l_new) *
            has_ptr_permission(&t)
      */
    }
  }
}





























