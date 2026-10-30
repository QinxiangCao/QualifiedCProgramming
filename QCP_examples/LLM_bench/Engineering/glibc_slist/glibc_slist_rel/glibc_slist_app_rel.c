#include "glibc_slist_clean_data.h"

/*@ Import Coq Require Import glibc_slist_app_rel_lib */
/*@ Extern Coq 
               (glibc_slist_clean_app_M: list Z -> list Z -> program unit (list Z))
               (residual_prog_in_glibc_slist_clean_app_M_call_1: list Z -> program unit (list Z))
                */

struct list *glibc_slist_clean_app(struct list *x, struct list *y)
/*@ high_level_spec <= low_level_spec
    With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(l1, l2))
 */;
struct list *glibc_slist_clean_app(struct list *x, struct list *y)
/*@
    low_level_spec
    With X l1 l2
    Require safeExec(ATrue, glibc_slist_clean_app_M(l1, l2), X) && sll(x, l1) * sll(y, l2)
    Ensure exists l3, safeExec(ATrue, return(l3), X) && sll(__return, l3)
 */
{
    /*@ safeExec(ATrue, bind(list_append_raw_M(l1, l2), residual_prog_in_glibc_slist_clean_app_M_call_1), X) && sll(x, l1) * sll(y, l2) */
    return list_append_raw(x, y) /*@ where(low_level_spec_aux) {B = (list Z)} X = X */;
}
