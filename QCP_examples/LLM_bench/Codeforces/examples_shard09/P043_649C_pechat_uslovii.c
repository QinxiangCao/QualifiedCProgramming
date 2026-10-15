/*
 * Codeforces 649/C - Printing Statements  (rating 1500, GREEDY)
 *
 * Serving the cheapest sets first maximises the count.  For one set, spend
 * double-sided sheets first (they cover two pages each) and finish the tail
 * with single-sided ones; that consumes the least paper for that set.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P043-solver-support */
/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P043_649C_pechat_uslovii_lib */
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (Spec : list Z -> Z -> Z -> Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P043-solver-support */

/*@ Extern Coq
      (PrefixResourceState : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 200000 &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        IntArray::full(arr, n, l1)
*/
;

// static int cmp_int(const void *a, const void *b)
// {
//     int x = *(const int *)a, y = *(const int *)b;
//     return (x > y) - (x < y);
// }

/* solver: maximum number of teams served.  Sorts a[] ascending. */
static int solver(int *a, int n, long long x, long long y)
/* QCP_INSERT_BEGIN:shard09-P043-solver-contract */
/*@ With (page_counts : list Z)
    Require
      x >= 0 && y >= 0 &&
      1 <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (1 <= page_counts[i] && page_counts[i] <= 10000)) &&
      n == Zlength(page_counts) && IntArray::full(a, n, page_counts)
    Ensure
      Spec(page_counts, x@pre, y@pre, __return) &&
      exists (pages_after : list Z), Permutation(page_counts, pages_after) && IntArray::full(a, n, pages_after)
*/
/* QCP_INSERT_END:shard09-P043-solver-contract */
{
    // qsort(a, n, sizeof *a, cmp_int);
    quicksort(a, n);
    int served = 0;
    /*@ Inv Assert
          exists sorted_pages,
            a == a@pre && n == n@pre &&
            1 <= n@pre && n@pre <= 200000 &&
            Zlength(sorted_pages) == n@pre &&
            0 <= i && i <= n@pre && served == i &&
            0 <= x && x <= x@pre && 0 <= y && y <= y@pre &&
            (forall j, (0 <= j && j < n@pre) =>
              (1 <= sorted_pages[j] && sorted_pages[j] <= 10000)) &&
            Permutation(page_counts, sorted_pages) &&
            mono_nondec(sorted_pages) &&
            PrefixResourceState(sorted_pages, x@pre, y@pre, i, x, y) &&
            IntArray::full(a, n@pre, sorted_pages)
    */
    for (int i = 0; i < n; i++) {
        long long pages = a[i];
        long long use = pages / 2;
        if (use > x)
            use = x;
        x -= use;
        pages -= 2 * use;
        if (pages > 0) {
            if (pages <= y)
                y -= pages;               /* finish on single-sided sheets */
            else if (pages == 1 && x > 0)
                x--;                      /* one page on a fresh double sheet */
            else
                break;
        }
        served++;
    }
    /*@ Assert
          exists sorted_pages,
            a == a@pre && n == n@pre &&
            0 <= served && served <= n@pre &&
            Spec(page_counts, x@pre, y@pre, served) &&
            Permutation(page_counts, sorted_pages) &&
            store_int64(&x, x) *
            store_int64(&y, y) *
            IntArray::full(a, n@pre, sorted_pages)
    */
    return served;
}

// int main(void)
// {
//     int n;
//     long long x, y;
//     if (scanf("%d %lld %lld", &n, &x, &y) != 3)
//         return 0;
//     static int a[200005];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     printf("%d\n", solver(a, n, x, y));
//     return 0;
// }
