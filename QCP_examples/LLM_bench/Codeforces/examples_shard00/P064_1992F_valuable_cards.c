/* Codeforces 1992/F - Valuable Cards */
// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"

typedef unsigned long size_t;

/* QCP_INSERT_BEGIN:P064_1992F_valuable_cards.support */
/*@ Extern Coq
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (UCharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P064_1992F_valuable_cards_lib */
/* QCP_INSERT_END:P064_1992F_valuable_cards.support */

/*@ Extern Coq
      (ValuableOuterState : Z -> list Z -> Z -> Z -> list Z -> Prop)
      (ValuableClosureState : Z -> list Z -> Z -> list Z -> Z -> list Z -> Z -> Prop)
      (ValuableBitmap : Z -> list Z -> list Z -> Prop)
      (ValuableClearingState : Z -> list Z -> Z -> list Z -> Prop)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::seg_shape : Z -> Z -> Z -> Assertion)
*/

/*@ Extern Coq
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/

/*@ Extern Coq
      (ValuableForcedHistory : Z -> list Z -> Z -> Z -> list Z -> Prop)
*/

/*@ Extern Coq
      (ValuableAlignedHistory : Z -> list Z -> Z -> Z -> list Z -> Prop)
*/

void *calloc(unsigned long nmemb, unsigned long size)
/*@ calloc_uchar
    With (cells : Z)
    Require
      0 <= cells && cells <= INT_MAX &&
      nmemb == cells && size == 1
    Ensure
      __return != 0 &&
      UCharArray::full(__return, cells, repeat_Z(0, cells))
*/;

void *malloc(unsigned long size)
/*@ malloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      size == cap * sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::undef_full(__return, cap)
*/;

void free(void *ptr)
/*@ free_uchar
    With (cells : Z) (values : list Z)
    Require
      0 <= cells && Zlength(values) == cells &&
      UCharArray::full(ptr, cells, values)
    Ensure emp
*/
/*@ free_int_split
    With (cap : Z) (count : Z) (values : list Z)
    Require
      0 <= count && count <= cap && Zlength(values) == count &&
      IntArray::seg(ptr, 0, count, values) *
      IntArray::undef_seg(ptr, count, cap)
    Ensure emp
*/;

static int solver(const int *a, int n,
                  int x) /* QCP_INSERT_BEGIN:P064_1992F_valuable_cards.contract */

/*@ With (values : list Z)
    Require
      2 <= x && x <= 100000 &&
      1 <= Zlength(values) && Zlength(values) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 200000)) &&
      Pre(x, values) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(x, values, __return) && IntArray::full(a, n, values)
*/
/* QCP_INSERT_END:P064_1992F_valuable_cards.contract */
{
    unsigned char *used = calloc((size_t)x + 1, 1)
        /*@ where (calloc_uchar) cells = x + 1 */;
    int *products_buf = malloc((size_t)(x + 1) * sizeof(*products_buf))
        /*@ where (malloc_int) cap = x + 1 */;
    int count = 1, segments = 1;
    products_buf[0] = 1;
    used[1] = 1;
    /*@ Inv Assert
          exists products bitmap,
            a == a@pre && n == n@pre && x == x@pre &&
            n@pre == Zlength(values) &&
            2 <= x@pre && x@pre <= 100000 &&
            1 <= Zlength(values) && Zlength(values) <= 100000 &&
            (forall k, (0 <= k && k < Zlength(values)) =>
              (1 <= values[k] && values[k] <= 200000)) &&
            Pre(x@pre, values) &&
            0 <= i && i <= n@pre &&
            1 <= segments && segments <= i + 1 &&
            count == Zlength(products) && 1 <= count && count <= x@pre &&
            Zlength(bitmap) == x@pre + 1 &&
            (forall k, (0 <= k && k < count) =>
              (1 <= products[k] && products[k] <= x@pre)) &&
            ValuableOuterState(x@pre, values, i, segments, products) &&
            ValuableForcedHistory(x@pre, values, i, segments, products) &&
            ValuableAlignedHistory(x@pre, values, i, segments, products) &&
            ValuableBitmap(x@pre, products, bitmap) &&
            IntArray::full(a@pre, n@pre, values) *
            IntArray::seg(products_buf, 0, count, products) *
            IntArray::undef_seg(products_buf, count, x@pre + 1) *
            UCharArray::full(used, x@pre + 1, bitmap)
    */
    for (int i = 0; i < n; ++i)
    {
        int v = a[i];
        if (x % v)
            continue;
        int old = count, reaches = 0;
        /*@ Inv Assert
              exists segment base_products products bitmap,
                a == a@pre && n == n@pre && x == x@pre &&
                n@pre == Zlength(values) &&
                2 <= x@pre && x@pre <= 100000 &&
                1 <= Zlength(values) && Zlength(values) <= 100000 &&
                (forall k, (0 <= k && k < Zlength(values)) =>
                  (1 <= values[k] && values[k] <= 200000)) &&
                Pre(x@pre, values) &&
                0 <= i && i < n@pre &&
                v == values[i] && 1 <= v && v <= x@pre && x@pre % v == 0 &&
                1 <= segments && segments <= i + 1 &&
                old == Zlength(base_products) &&
                base_products == sublist(0, old, products) &&
                1 <= old && old <= count && count <= x@pre &&
                0 <= j && j <= old &&
                count == Zlength(products) &&
                (reaches == 0 || reaches == 1) &&
                Zlength(bitmap) == x@pre + 1 &&
                (forall k, (0 <= k && k < count) =>
                  (1 <= products[k] && products[k] <= x@pre)) &&
                ValuableOuterState(x@pre, values, i, segments, base_products) &&
                ValuableForcedHistory(x@pre, values, i, segments, base_products) &&
                ValuableAlignedHistory(x@pre, values, i, segments, base_products) &&
                ValuableClosureState(x@pre, segment, v, base_products,
                  j, products, reaches) &&
                ValuableBitmap(x@pre, products, bitmap) &&
                IntArray::full(a@pre, n@pre, values) *
                IntArray::seg(products_buf, 0, count, products) *
                IntArray::undef_seg(products_buf, count, x@pre + 1) *
                UCharArray::full(used, x@pre + 1, bitmap)
        */
        for (int j = 0; j < old; ++j)
            /*@ Given products_before_append from products */
            if (products_buf[j] <= x / v && x % (products_buf[j] * v) == 0)
            {
                int p = products_buf[j] * v;
                /*@ 1 <= p && p <= x by local */
                if (!used[p])
                {
                    used[p] = 1;
                    products_buf[count] = p;
                    /*@ IntArray::seg(products_buf, 0, count + 1,
                          app(products_before_append, cons(p, nil))) */
                    ++count;
                }
                if (p == x)
                    reaches = 1;
            }
        /*@ Assert
              exists segment base_products products bitmap,
                a == a@pre && n == n@pre && x == x@pre &&
                n@pre == Zlength(values) &&
                2 <= x@pre && x@pre <= 100000 &&
                1 <= Zlength(values) && Zlength(values) <= 100000 &&
                (forall k, (0 <= k && k < Zlength(values)) =>
                  (1 <= values[k] && values[k] <= 200000)) &&
                Pre(x@pre, values) &&
                0 <= i && i < n@pre &&
                v == values[i] && 1 <= v && v <= x@pre && x@pre % v == 0 &&
                1 <= segments && segments <= i + 1 &&
                old == Zlength(base_products) &&
                base_products == sublist(0, old, products) &&
                1 <= old && old <= count && count <= x@pre &&
                count == Zlength(products) &&
                (reaches == 0 || reaches == 1) &&
                Zlength(bitmap) == x@pre + 1 &&
                (forall k, (0 <= k && k < count) =>
                  (1 <= products[k] && products[k] <= x@pre)) &&
                ValuableOuterState(x@pre, values, i, segments, base_products) &&
                ValuableForcedHistory(x@pre, values, i, segments, base_products) &&
                ValuableAlignedHistory(x@pre, values, i, segments, base_products) &&
                ValuableClosureState(x@pre, segment, v, base_products,
                  old, products, reaches) &&
                ValuableBitmap(x@pre, products, bitmap) &&
                IntArray::full(a@pre, n@pre, values) *
                IntArray::seg(products_buf, 0, count, products) *
                IntArray::undef_seg(products_buf, count, x@pre + 1) *
                UCharArray::full(used, x@pre + 1, bitmap)
        */
        if (reaches)
        {
            ++segments;
            /*@ Inv Assert
                  exists segment base_products products bitmap,
                    a == a@pre && n == n@pre && x == x@pre &&
                    n@pre == Zlength(values) &&
                    2 <= x@pre && x@pre <= 100000 &&
                    1 <= Zlength(values) && Zlength(values) <= 100000 &&
                    (forall k, (0 <= k && k < Zlength(values)) =>
                      (1 <= values[k] && values[k] <= 200000)) &&
                    Pre(x@pre, values) &&
                    0 <= i && i < n@pre &&
                    v == values[i] && 1 <= v && v <= x@pre && x@pre % v == 0 &&
                    2 <= segments && segments <= i + 2 &&
                    old == Zlength(base_products) &&
                    base_products == sublist(0, old, products) &&
                    count == Zlength(products) && 1 <= count && count <= x@pre &&
                    0 <= j && j <= count &&
                    reaches == 1 &&
                    Zlength(bitmap) == x@pre + 1 &&
                    (forall k, (0 <= k && k < count) =>
                      (1 <= products[k] && products[k] <= x@pre)) &&
                    ValuableOuterState(x@pre, values, i, segments - 1, base_products) &&
                    ValuableForcedHistory(x@pre, values, i, segments - 1, base_products) &&
                    ValuableAlignedHistory(x@pre, values, i, segments - 1, base_products) &&
                    ValuableClosureState(x@pre, segment, v, base_products,
                      old, products, 1) &&
                    ValuableClearingState(x@pre, products, j, bitmap) &&
                    IntArray::full(a@pre, n@pre, values) *
                    IntArray::seg(products_buf, 0, count, products) *
                    IntArray::undef_seg(products_buf, count, x@pre + 1) *
                    UCharArray::full(used, x@pre + 1, bitmap)
            */
            for (int j = 0; j < count; ++j)
                used[products_buf[j]] = 0;
            count = 1;
            products_buf[0] = 1;
            used[1] = 1;
            /*@ Assert
                  exists segment base_products old_products bitmap,
                    a == a@pre && n == n@pre && x == x@pre &&
                    n@pre == Zlength(values) &&
                    2 <= x@pre && x@pre <= 100000 &&
                    1 <= Zlength(values) && Zlength(values) <= 100000 &&
                    (forall k, (0 <= k && k < Zlength(values)) =>
                      (1 <= values[k] && values[k] <= 200000)) &&
                    Pre(x@pre, values) &&
                    0 <= i && i < n@pre &&
                    v == values[i] && 1 <= v && v <= x@pre && x@pre % v == 0 &&
                    2 <= segments && segments <= i + 2 &&
                    old == Zlength(base_products) &&
                    base_products == sublist(0, old, old_products) &&
                    count == 1 && 1 <= count && count <= x@pre &&
                    reaches == 1 &&
                    ValuableOuterState(x@pre, values, i, segments - 1, base_products) &&
                    ValuableForcedHistory(x@pre, values, i, segments - 1, base_products) &&
                    ValuableAlignedHistory(x@pre, values, i, segments - 1, base_products) &&
                    ValuableClosureState(x@pre, segment, v, base_products,
                      old, old_products, 1) &&
                    Zlength(bitmap) == x@pre + 1 &&
                    ValuableBitmap(x@pre, cons(1, nil), bitmap) &&
                    IntArray::full(a@pre, n@pre, values) *
                    IntArray::seg(products_buf, 0, count, cons(1, nil)) *
                    IntArray::undef_seg(products_buf, count, x@pre + 1) *
                    UCharArray::full(used, x@pre + 1, bitmap)
            */
            /*@ 0 <= v && v < x + 1 by local */
            if (!used[v])
            {
                used[v] = 1;
                products_buf[count] = v;
                /*@ IntArray::seg(products_buf, 0, count + 1,
                      cons(1, cons(v, nil))) */
                ++count;
            }
        }
    }
    /*@ Assert
          exists products bitmap,
            a == a@pre && n == n@pre && x == x@pre &&
            n@pre == Zlength(values) &&
            Spec(x@pre, values, segments) &&
            ValuableAlignedHistory(x@pre, values, n@pre, segments, products) &&
            count == Zlength(products) && 1 <= count && count <= x@pre &&
            Zlength(bitmap) == x@pre + 1 &&
            IntArray::full(a@pre, n@pre, values) *
            IntArray::seg(products_buf, 0, count, products) *
            IntArray::undef_seg(products_buf, count, x@pre + 1) *
            UCharArray::full(used, x@pre + 1, bitmap)
    */
    free(used)
        /*@ where (free_uchar) cells = x + 1 */;
    free(products_buf)
        /*@ where (free_int_split) cap = x + 1, count = count */;
    return segments;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n, x;
//         scanf("%d %d", &n, &x);
//         int *a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i)
//             scanf("%d", &a[i]);
//         printf("%d\n", solver(a, n, x));
//         free(a);
//     }
//     return 0;
// }
