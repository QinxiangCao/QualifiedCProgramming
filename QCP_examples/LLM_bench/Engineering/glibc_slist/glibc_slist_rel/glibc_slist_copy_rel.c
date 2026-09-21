#include "glibc_slist_clean_data.h"

/*@ Import Coq Require Import glibc_slist_copy_rel_lib */
/*@ Extern Coq (early_result :: * => * => *) */
/*@ Extern Coq (glibc_slist_clean_copy_result: list Z -> list Z -> Prop) */
/*@ Extern Coq 
               (maketuple: {A} {B} -> A -> B -> (A * B))
               (glibc_slist_clean_copy_M: list Z -> program unit (list Z * list Z))
               (glibc_slist_clean_copy_M_loop: list Z -> list Z -> list Z -> program unit (early_result (list Z * list Z) (list Z * list Z)))
               (glibc_slist_clean_copy_M_loop_end: (list Z * list Z) -> program unit (list Z * list Z))
               (glibc_slist_clean_copy_M_after_loop: early_result (list Z * list Z) (list Z * list Z) -> program unit (list Z * list Z))
               (residual_prog_in_glibc_slist_clean_copy_M_call_1: list Z -> Z -> list Z -> list Z -> program unit ((list Z * list Z)))
                */

struct list *glibc_slist_clean_copy(struct list *src)
/*@ high_level_spec <= low_level_spec
    With l1
    Require sll(src, l1)
    Ensure exists l2, glibc_slist_clean_copy_result(l1, l2) && sll(src@pre, l1) * sll(__return, l2)
 */;
struct list *glibc_slist_clean_copy(struct list *src)
/*@
    low_level_spec
    With X l1
    Require safeExec(ATrue, glibc_slist_clean_copy_M(l1), X) && sll(src, l1)
    Ensure exists l2 l3, safeExec(ATrue, return(maketuple(l2, l3)), X) && sll(src@pre, l2) * sll(__return, l3)
 */
{
    struct list *dst;
    struct list *node;
    struct list *copy;

    dst = 0;
    node = src;
    /*@ Inv exists l1 l2 l3, safeExec(ATrue, bind(glibc_slist_clean_copy_M_loop(l1,l2,l3), glibc_slist_clean_copy_M_after_loop), X) && src == src@pre && undef_data_at(&copy, struct list*) * sllseg(src@pre, node, l1) * sll(node, l2) * sll(dst, l3) */
    while (node != 0) {
        copy = malloc_list_node(node->data);
        if (copy == 0) {
            glibc_slist_clean_free(dst);
            return 0;
        }

        /*@ exists lprefix lrest ldst v, safeExec(ATrue, bind(list_append_raw_M(ldst, cons(v, nil)), residual_prog_in_glibc_slist_clean_copy_M_call_1(lprefix, v, lrest)), X) && src == src@pre && node != 0 && node -> data == v && copy != 0 && sllseg(src@pre, node, lprefix) * sll(node -> next, lrest) * sll(dst, ldst) * sll(copy, cons(v, nil)) */
        dst = list_append_raw(dst, copy) /*@ where(low_level_spec_aux) X = X; B = (list Z * list Z) */;
        node = node->next;
    }
    return dst;
}
