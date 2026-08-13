#include "pos_int_pair.h"

int diffx1(struct int_pair *p, struct int_pair *q)
/*@ With px py qx qy
    Require store_pos_int_pair(p, px, py) *
            store_pos_int_pair(q, qx, qy)
    Ensure __return == px - qx &&
           store_pos_int_pair(p, px, py) *
           store_pos_int_pair(q, qx, qy)
 */
{
    /*@ do pair_range */
    int temp = p->a - q->a;
    return temp;
}

int diffx2(struct int_pair *p, struct int_pair *q)
/*@ With px py qx qy
    Require store_pos_int_pair(p, px, py) *
            store_pos_int_pair(q, qx, qy)
    Ensure __return == px - qx &&
           store_pos_int_pair(p, px, py) *
           store_pos_int_pair(q, qx, qy)
 */
{
    /*@ Assert px >= 0 && qx >= 0 &&
               px <= INT_MAX && qx <= INT_MAX &&
               p == p@pre && q == q@pre &&
               store_pos_int_pair(p, px, py) *
               store_pos_int_pair(q, qx, qy) by pair_range */
    int temp = p->a - q->a;
    return temp;
}

int getx(struct int_pair *p)
/*@ With x y
    Require store_pos_int_pair(p, x, y)
    Ensure __return >= 0 &&
           store_pos_int_pair(p, x, y)
 */
{
    return p->a /*@ by pair_range */;
}

void slow_sub(struct int_pair *p)
/*@ With x y
    Require x >= y && store_pos_int_pair(p, x, y)
    Ensure store_pos_int_pair(p, x - y, 0)
 */
{
    /*@ Inv Assert exists x0 y0,
          x >= y && x0 >= 0 && y0 >= 0 && p == p@pre &&
          x - x0 == y - y0 && x >= x0 && store_pos_int_pair(p, x0, y0)
        by pair_range */
    while (p->b != 0) {
        p->a --;
        p->b --;
    }
}

void swap(struct int_pair *p)
/*@ With x y
    Require store_pos_int_pair(p, x, y)
    Ensure store_pos_int_pair(p, y, x)
 */
{
    /*@ do unfold */
    int temp = p->a;
    p->a = p->b;
    p->b = temp;
    /*@ do fold */
}

void swap2(struct int_pair *p)
/*@ With x y
    Require store_pos_int_pair(p, x, y)
    Ensure store_pos_int_pair(p, y, x)
 */
{
    /*@ Assert x >= 0 && y >= 0 && p == p@pre &&
               store_pos_int_pair(p, x, y) by pair_range */
    int temp = p->a;
    p->a = p->b;
    p->b = temp;
}

