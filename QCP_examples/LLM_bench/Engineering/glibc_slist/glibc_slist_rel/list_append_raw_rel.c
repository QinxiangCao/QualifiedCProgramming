#include "glibc_slist_clean_data.h"

/*@ Import Coq Require Import list_append_raw_rel_lib */
/*@ Extern Coq (early_result :: * => * => *) */
/*@ Extern Coq 
               (list_append_raw_M: list Z -> list Z -> program unit (list Z))
               (residual_prog_in_list_append_raw_M_call_1: list Z -> list Z * Z -> program unit (list Z))
                */

struct list *list_append_raw(struct list *x, struct list *y)
/*@ high_level_spec <= low_level_spec
    With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(l1, l2))
 */;
struct list *list_append_raw(struct list *x, struct list *y)
/*@
    low_level_spec
    With X l1 l2
    Require safeExec(ATrue, list_append_raw_M(l1, l2), X) && sll(x, l1) * sll(y, l2)
    Ensure exists l3, safeExec(ATrue, return(l3), X) && sll(__return, l3)
 */
{
    struct list *tail;

    if (x == 0) {
        return y;
    }

    /*@ safeExec(ATrue, bind(list_tail_M(l1), residual_prog_in_list_append_raw_M_call_1(l2)), X) && x != 0 && sll(x, l1) * sll(y, l2) */
    tail = list_tail(x) /*@ where(low_level_spec_aux) X = X; B = (list Z) */;
    tail->next = y;
    return x;
}
