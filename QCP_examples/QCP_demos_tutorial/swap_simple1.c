/*@ Import Coq Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib */

/*@ Extern Coq (store_int_pair : Z -> Z -> Z -> Assertion) */

struct int_pair {
    int a;
    int b;
};

void swap_int_pair(struct int_pair *p)
/*@ With x y
    Require store_int_pair(p, x, y)
    Ensure store_int_pair(p, y, x)
 */
{
    /*@ Assert
          p == p@pre && store(&(p->a), x) * store(&(p->b), y)
     */
    int temp = p->a;
    p->a = p->b;
    p->b = temp;
}
