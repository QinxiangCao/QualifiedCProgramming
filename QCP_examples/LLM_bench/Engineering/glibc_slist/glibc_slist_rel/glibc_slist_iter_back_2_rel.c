#include "glibc_slist_clean_data.h"

/*@ Import Coq Require Import glibc_slist_iter_back_2_rel_lib */
/*@ Extern Coq 
               (maketuple: {A} {B} -> A -> B -> (A * B))
               (glibc_slist_clean_iter_back_2_M: list Z -> program unit (list Z * Z))
               (glibc_slist_clean_iter_back_2_M_loop1: list Z -> Z -> program unit (list Z * Z))
               (glibc_slist_clean_iter_back_2_M_loop2: list Z -> Z -> program unit (list Z * Z))
               (glibc_slist_clean_iter_back_2_M_loop2_cont: list Z -> list Z -> Z -> (list Z * Z) -> program unit (list Z * Z))
               (glibc_slist_clean_iter_back_2_M_loop1_end: list Z -> (list Z * Z) -> program unit (list Z * Z))
               (glibc_slist_clean_iter_back_2_prev_case: Z -> list Z -> Z -> Z -> Prop)
	               (range: list Z -> Prop)
	                */
/*@ Extern Coq (list_sum: list Z -> Z) */

long glibc_slist_clean_iter_back_2(struct list *x)
/*@ high_level_spec <= low_level_spec
    With l1
    Require range(l1) && sllseg(x, 0, l1)
    Ensure __return == list_sum(l1) && sll(x@pre, l1)
 */;
long glibc_slist_clean_iter_back_2(struct list *x)
/*@ low_level_spec
    With X l1
    Require range(l1) && safeExec(ATrue, glibc_slist_clean_iter_back_2_M(l1), X) && sllseg(x, 0, l1)
    Ensure exists l2 r, safeExec(ATrue, return(maketuple(l2, r)), X) && __return == r && sll(x@pre, l2)
 */
{
    struct list *stop;
    struct list *prev;
    struct list *node;
    long sum;

    stop = 0;
    sum = 0;
	    /*@ Inv exists st s l1_1 ldone, safeExec(ATrue, bind(glibc_slist_clean_iter_back_2_M_loop1(l1_1,s), glibc_slist_clean_iter_back_2_M_loop1_end(app(l1_1, ldone))), X) && x == x@pre && range(l1_1) && -2147483648 <= s && s <= 2147483647 && undef_data_at(&prev, struct list*) * undef_data_at(&node, struct list*) * store(&stop, struct list*, st) * store(&sum, long, s) * sllseg(x@pre, st, l1_1) * sll(st, ldone) */
	    while (x != stop) {
	        prev = 0;
	        node = x;
		        
		        /*@ Inv Assert exists p st s lpre l2_1 ldone y v lrest, l2_1 == cons(v, lrest) && safeExec(ATrue, bind(glibc_slist_clean_iter_back_2_M_loop2(l2_1,s), glibc_slist_clean_iter_back_2_M_loop2_cont(app(app(lpre, l2_1), ldone), app(lpre, l2_1), s)), X) && x == x@pre && node != 0 && x != st && range(lpre) && range(l2_1) && range(app(lpre, l2_1)) && range(l1) && -2147483648 <= s && s <= 2147483647 && glibc_slist_clean_iter_back_2_prev_case(p, lpre, node, x@pre) && store(&prev, struct list*, p) * store(&stop, struct list*, st) * store(&sum, long, s) * sllseg(x@pre, node, lpre) * store(&(node->next), struct list*, y) * store(&(node->data), int, v) * sllseg(y, st, lrest) * sll(st, ldone) */
        while (node->next != stop) {
            prev = node;
            node = node->next;
        }
        sum += node->data;
        stop = node;
        if (prev == 0) {
            /*@ Assert exists ldone v, safeExec(ATrue, return(maketuple(cons(v, ldone), sum)), X) && node == x@pre && node != 0 && store(&x, struct list*, x@pre) * store(&prev, struct list*, 0) * store(&stop, struct list*, node) * sll(node, cons(v, ldone)) */
            break;
        }
    }
    return sum;
}
