// #include <stdio.h>
typedef long long i64;
/*@ Extern Coq
      (MaxResult : Z -> Z -> Z -> Prop)
      (MinResult : Z -> Z -> Z -> Prop)
      (QuotientBlock : Z -> Z -> Z -> Z -> Prop)
      (CandyFeasibleInterval : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (CandySearchPrefix : Z -> Z -> Z -> Z -> Z -> Prop)
      (CandySearchBlock : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (CandyArithmeticBest : Z -> Z -> Z -> Z -> Prop)
*/
static i64 maxll(i64 a, i64 b)
/*@
    Require
      -1000000000000 <= a && a <= 1000000000000 &&
      -1000000000000 <= b && b <= 1000000000000
    Ensure
      MaxResult(a, b, __return)
*/
{
    return a > b ? a : b;
}
static i64 minll(i64 a, i64 b)
/*@
    Require
      -1000000000000 <= a && a <= 1000000000000 &&
      -1000000000000 <= b && b <= 1000000000000
    Ensure
      MinResult(a, b, __return)
*/
{
    return a < b ? a : b;
}
static i64 ceildiv(i64 a, i64 b)
/*@
    Require
      -1000000000000 <= a && a <= 1000000000000 &&
      1 <= b && b <= 1000000000000
    Ensure
      (__return - 1) * b < a && a <= __return * b
*/
{
    if (a <= 0)
        return a / b;
    return (a + b - 1) / b;
}
static void check(i64 L, i64 R, i64 q, i64 n, i64 x, i64 k, i64 add, i64 *best)
/*@ With (old_best : Z)
    Require
      1 <= n && n <= 100000000000 &&
      1 <= x && x <= n &&
      1 <= k && k <= 100000000000 &&
      n <= L && L <= R && R <= 2 * n &&
      0 <= q && q <= k - 1 &&
      QuotientBlock(k, L, R, q) &&
      -1 <= old_best && old_best <= n &&
      0 <= add && add <= 1 &&
      CandySearchBlock(n, x, k, L, R, add, old_best) &&
      store_int64(best, old_best)
    Ensure
      exists new_best,
        -1 <= new_best && new_best <= n &&
        CandySearchBlock(n, x, k, L, R, add + 1, new_best) &&
        store_int64(best, new_best)
*/
{
    i64 c = k - x + add, lo = L, hi = R;
    /* y = c-q*num; add=0 is normal, add=1 is the one-candy sweet last child. */
    if (q)
    {
        hi = minll(hi, (add ? c - 1 : c) / q);
        lo = maxll(lo, ceildiv(c - x, q));
    }
    else if ((add && c < 1) || (!add && c < 0) || c > x)
        return;
    lo = maxll(lo, ceildiv(c + n, q + 1));
    hi = minll(hi, (c + 2 * n - x) / (q + 1));
    /*@ Assert
        L == L@pre && R == R@pre && q == q@pre && n == n@pre &&
        x == x@pre && k == k@pre && add == add@pre && best == best@pre &&
        1 <= n@pre && n@pre <= 100000000000 &&
        1 <= x@pre && x@pre <= n@pre &&
        1 <= k@pre && k@pre <= 100000000000 &&
        n@pre <= L@pre && L@pre <= R@pre && R@pre <= 2 * n@pre &&
        0 <= q@pre && q@pre <= k@pre - 1 &&
        0 <= add@pre && add@pre <= 1 &&
        c == k@pre - x@pre + add@pre &&
        L@pre <= lo && hi <= R@pre &&
        -1 <= old_best && old_best <= n@pre &&
        QuotientBlock(k@pre, L@pre, R@pre, q@pre) &&
        CandyFeasibleInterval(n@pre, x@pre, k@pre, L@pre, R@pre,
                              q@pre, add@pre, lo, hi) &&
        CandySearchBlock(n@pre, x@pre, k@pre, L@pre, R@pre,
                         add@pre, old_best) &&
        store_int64(best@pre, old_best)
     */
    if (lo <= hi && hi - n > *best)
        *best = hi - n;
}
/* QCP_INSERT_BEGIN:P091_1063D_candies_for_children.support */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P091_1063D_candies_for_children_lib */
/* QCP_INSERT_END:P091_1063D_candies_for_children.support */
static i64 solver(i64 n, i64 l, i64 r,
                  i64 k) /* QCP_INSERT_BEGIN:P091_1063D_candies_for_children.contract */

/*@
    Require
      1 <= n && n <= 100000000000 &&
      1 <= k && k <= 100000000000 &&
      1 <= l && l <= n &&
      1 <= r && r <= n
    Ensure
      Spec(n, l, r, k, __return)
*/
/* QCP_INSERT_END:P091_1063D_candies_for_children.contract */
{
    i64 x = (r - l + n) % n + 1, z = k - 1, best = -1;
    /*@ Inv Assert
        n == n@pre && l == l@pre && r == r@pre && k == k@pre &&
        x == (r@pre - l@pre + n@pre) % n@pre + 1 &&
        z == k@pre - 1 &&
        1 <= n@pre && n@pre <= 100000000000 &&
        1 <= k@pre && k@pre <= 100000000000 &&
        1 <= l@pre && l@pre <= n@pre &&
        1 <= r@pre && r@pre <= n@pre &&
        1 <= x && x <= n@pre &&
        n@pre <= cur && cur <= 2 * n@pre &&
        -1 <= best && best <= n@pre &&
        CandySearchPrefix(n@pre, x, k@pre, cur, best)
     */
    for (i64 cur = n; cur <= 2 * n;)
    {
        i64 q = z / cur, R = q ? z / q : 2 * n;
        if (R > 2 * n)
            R = 2 * n;
        /*@ Assert
            n == n@pre && l == l@pre && r == r@pre && k == k@pre &&
            x == (r@pre - l@pre + n@pre) % n@pre + 1 &&
            z == k@pre - 1 && q == z / cur &&
            1 <= n@pre && n@pre <= 100000000000 &&
            1 <= k@pre && k@pre <= 100000000000 &&
            1 <= l@pre && l@pre <= n@pre &&
            1 <= r@pre && r@pre <= n@pre &&
            1 <= x && x <= n@pre &&
            n@pre <= cur && cur <= R && R <= 2 * n@pre &&
            0 <= q && q <= k@pre - 1 &&
            QuotientBlock(k@pre, cur, R, q) &&
            -1 <= best && best <= n@pre &&
            CandySearchBlock(n@pre, x, k@pre, cur, R, 0, best)
         */
        check(cur, R, q, n, x, k, 0, &best) /*@ where old_best = best */;
        check(cur, R, q, n, x, k, 1, &best) /*@ where old_best = best */;
        /*@ Assert
            n == n@pre && l == l@pre && r == r@pre && k == k@pre &&
            x == (r@pre - l@pre + n@pre) % n@pre + 1 &&
            z == k@pre - 1 &&
            1 <= n@pre && n@pre <= 100000000000 &&
            1 <= k@pre && k@pre <= 100000000000 &&
            1 <= l@pre && l@pre <= n@pre &&
            1 <= r@pre && r@pre <= n@pre &&
            1 <= x && x <= n@pre &&
            n@pre <= cur && cur <= R && R <= 2 * n@pre &&
            q == z / cur && 0 <= q && q <= k@pre - 1 &&
            -1 <= best && best <= n@pre &&
            CandySearchPrefix(n@pre, x, k@pre, R + 1, best)
         */
        if (R == 2 * n)
            break;
        cur = R + 1;
    }
    return best;
}
// int main(void)
// {
//     i64 n, l, r, k;
//     if (scanf("%lld%lld%lld%lld", &n, &l, &r, &k) != 4)
//         return 0;
//     printf("%lld\n", solver(n, l, r, k));
//     return 0;
// }
