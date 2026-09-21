#include "glibc_slist_clean_data.h"

/*@ Import Coq Require Import glibc_slist_multi_append_rel_lib */
/*@ Extern Coq 
               (glibc_slist_clean_multi_append_M: list Z -> list Z -> list Z -> program unit (list Z))
               (residual_prog_in_glibc_slist_clean_multi_append_M_call_1: list Z -> list Z -> program unit (list Z))
               (residual_prog_in_glibc_slist_clean_multi_append_M_call_2: list Z -> program unit (list Z))
                */

struct list *glibc_slist_clean_multi_append(struct list *x, struct list *y,
                                            struct list *z)
/*@ high_level_spec <= low_level_spec
    With l1 l2 l3
    Require sll(x, l1) * sll(y, l2) * sll(z, l3)
    Ensure sll(__return, app(app(l1, l2), l3))
 */;
struct list *glibc_slist_clean_multi_append(struct list *x, struct list *y,
                                            struct list *z)
/*@ low_level_spec
    With X l1 l2 l3
    Require safeExec(ATrue, glibc_slist_clean_multi_append_M(l1, l2, l3), X) && sll(x, l1) * sll(y, l2) * sll(z, l3)
    Ensure exists l4, safeExec(ATrue, return(l4), X) && sll(__return, l4)
 */
{
    /*@ safeExec(ATrue, bind(list_append_raw_M(l1, l2), residual_prog_in_glibc_slist_clean_multi_append_M_call_1(l3)), X) && sll(x, l1) * sll(y, l2) * sll(z, l3) */
    x = list_append_raw(x, y) /*@ where(low_level_spec_aux) X = X; B = (list Z) */;
    
    /*@ exists l4, safeExec(ATrue, bind(list_append_raw_M(l4, l3), residual_prog_in_glibc_slist_clean_multi_append_M_call_2), X) && sll(x, l4) * sll(z, l3) */
    x = list_append_raw(x, z) /*@ where(low_level_spec_aux) X = X; B = (list Z) */;
    return x;
}
