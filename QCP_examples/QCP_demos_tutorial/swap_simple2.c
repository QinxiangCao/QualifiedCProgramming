#include "swap_simple2.h"

void swap_int_pair(struct int_pair *p)
/*@ With x y
    Require store_int_pair(p, x, y)
    Ensure store_int_pair(p, y, x)
 */
{
    int temp = p->a;
    p->a = p->b;
    p->b = temp;
}
