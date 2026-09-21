#include "glibc_slist_clean_data.h"

/*@ Import Coq Require Import glibc_slist_iter_back_rel_lib */
/*@ Extern Coq (early_result :: * => * => *) */
/*@ Extern Coq 
               (maketuple: {A} {B} -> A -> B -> (A * B))
               (glibc_slist_clean_iter_back_M: list Z -> program unit (list Z * Z))
               (residual_prog_in_glibc_slist_clean_iter_back_M_call_1: Z -> list Z * Z -> program unit ((list Z * Z)))
               (range: list Z -> Prop)
                */
/*@ Extern Coq (list_sum: list Z -> Z) */

long glibc_slist_clean_iter_back(struct list *x)
/*@ low_level_spec_aux <= low_level_spec
    With {B} (cont: (list Z * Z) -> program unit B) X l1
    Require range(l1) && safeExec(ATrue, bind(glibc_slist_clean_iter_back_M(l1), cont), X) && sll(x, l1)
    Ensure exists l2 r, safeExec(ATrue, bind(return(maketuple(l2, r)), cont), X) && __return == r && sll(x@pre, l2)
 */;
long glibc_slist_clean_iter_back(struct list *x)
/*@ high_level_spec <= low_level_spec
    With l1
    Require range(l1) && sll(x, l1)
    Ensure __return == list_sum(l1) && sll(x@pre, l1)
 */;
long glibc_slist_clean_iter_back(struct list *x)
/*@ low_level_spec
    With X l1
    Require range(l1) && safeExec(ATrue, glibc_slist_clean_iter_back_M(l1), X) && sll(x, l1)
    Ensure exists l2 r, safeExec(ATrue, return(maketuple(l2, r)), X) && __return == r && sll(x@pre, l2)
 */
{
    long sum;

    if (x == 0) {
        return 0;
    }

    /*@ Assert exists v ltail, x == x@pre && range(ltail) && safeExec(ATrue, bind(glibc_slist_clean_iter_back_M(ltail), residual_prog_in_glibc_slist_clean_iter_back_M_call_1(v)), X) && x != 0 && x -> data == v && undef_data_at(&sum, long) * sll(x -> next, ltail) */
    sum = glibc_slist_clean_iter_back(x->next) /*@ where(low_level_spec_aux) X = X; B = (list Z * Z) */;
    return sum + x->data;
}
