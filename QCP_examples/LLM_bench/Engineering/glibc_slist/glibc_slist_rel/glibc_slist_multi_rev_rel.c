#include "glibc_slist_clean_data.h"

/*@ Import Coq Require Import glibc_slist_multi_rev_rel_lib */
/*@ Extern Coq (MretTy :: *) */
/*@ Extern Coq 
               (rev_append_local_M: list Z -> list Z -> program unit (list Z))
               (rev_append_local_M_loop: list Z -> list Z -> program unit MretTy)
               (rev_append_local_M_loop_end: MretTy -> program unit (list Z))
               (glibc_slist_clean_multi_rev_M: list Z -> list Z -> program unit (list Z))
                */

static struct list *rev_append_local(struct list *src, struct list *dst)
/*@ low_level_spec_aux <= low_level_spec
    With {B} (cont: (list Z) -> program unit B) X l1 l2
    Require safeExec(ATrue, bind(rev_append_local_M(l1, l2), cont), X) && sll(src, l1) * sll(dst, l2)
    Ensure exists l3, safeExec(ATrue, bind(return(l3), cont), X) && sll(__return, l3)
 */;
static struct list *rev_append_local(struct list *src, struct list *dst)
/*@ low_level_spec
    With X l1 l2
    Require safeExec(ATrue, rev_append_local_M(l1, l2), X) && sll(src, l1) * sll(dst, l2)
    Ensure exists l3, safeExec(ATrue, return(l3), X) && sll(__return, l3)
 */
{
    struct list *node;

    /*@ Inv exists l1 l2, safeExec(ATrue, bind(rev_append_local_M_loop(l1,l2), rev_append_local_M_loop_end), X) && undef_data_at(&node, struct list*) * sll(src, l1) * sll(dst, l2) */
    while (src != 0) {
        node = src;
        src = src->next;
        node->next = dst;
        dst = node;
    }
    return dst;
}

struct list *glibc_slist_clean_multi_rev(struct list *x, struct list *y)
/*@ high_level_spec <= low_level_spec
    With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(rev(l2), rev(l1)))
 */;
struct list *glibc_slist_clean_multi_rev(struct list *x, struct list *y)
/*@ low_level_spec
    With X l1 l2
    Require safeExec(ATrue, glibc_slist_clean_multi_rev_M(l1, l2), X) && sll(x, l1) * sll(y, l2)
    Ensure exists l3, safeExec(ATrue, return(l3), X) && sll(__return, l3)
 */
{
    struct list *out;

    out = 0;
    /*@ safeExec(ATrue, bind(rev_append_local_M(l1, nil), rev_append_local_M(l2)), X) && sll(x, l1) * sll(out, nil) * sll(y, l2) */
    out = rev_append_local(x, out) /*@ where(low_level_spec_aux) X = X; B = (list Z) */;
    out = rev_append_local(y, out) /*@ where(low_level_spec) X = X */;
    return out;
}
