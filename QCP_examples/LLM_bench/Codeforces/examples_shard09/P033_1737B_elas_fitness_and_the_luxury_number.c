/*
 * Codeforces 1737/B - Ela's Fitness and the Luxury Number  (rating 1300, MATH)
 *
 * For s = floor(sqrt(x)), the luxurious numbers with that same s are exactly
 * s^2, s^2+s and s^2+2s.  So counting up to x gives 3*(s-1) complete blocks
 * below s, plus however many of those three do not exceed x.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P033-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P033_1737B_elas_fitness_and_the_luxury_number_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P033-solver-support */

/*@ Extern Coq
      (ISqrtSpec : Z -> Z -> Prop)
      (LuxuryCountUpto : Z -> Z -> Prop)
      (SqrtSearchBounds : Z -> Z -> Z -> Prop)
      (LuxuryBlockPrefix : Z -> Z -> Z -> Z -> Prop)
*/

/* isqrt: floor(sqrt(v)) for 0 <= v <= 1e18.  Binary search on the answer keeps
 * this in integers -- no math.h, and no double-rounding to correct for.  The
 * test is written as mid <= v / mid rather than mid * mid <= v, which would
 * overflow for mid above 3e9. */
static long long isqrt(long long v)
/*@ Require
      0 <= v && v <= 1000000000000000000 && emp
    Ensure
      ISqrtSpec(v@pre, __return) && emp
*/
{
    long long lo = 0, hi = 2000000000LL;  /* 2e9 > sqrt(1e18) = 1e9 */
    /*@ Inv Assert
          v == v@pre &&
          0 <= v@pre && v@pre <= 1000000000000000000 &&
          0 <= lo && lo <= hi && hi <= 2000000000 &&
          SqrtSearchBounds(v@pre, lo, hi) && emp
    */
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;   /* mid >= 1, so v / mid is safe */
        if (mid <= v / mid)
            lo = mid;
        else
            hi = mid - 1;
    }
    return lo;
}

/* solver: pure.  Count of luxurious numbers in [1, x]. */
static long long count_upto(long long x)
/*@ Require
      0 <= x && x <= 1000000000000000000 && emp
    Ensure
      0 <= __return && __return <= 3000000000 &&
      LuxuryCountUpto(x@pre, __return) && emp
*/
{
    if (x <= 0)
        return 0;
    long long s = isqrt(x), cnt = 3 * (s - 1);
    long long base = s * s;
    /*@ Inv Assert
          x == x@pre &&
          1 <= x@pre && x@pre <= 1000000000000000000 &&
          1 <= s && s <= 1000000000 &&
          ISqrtSpec(x@pre, s) &&
          base == s * s &&
          0 <= m && m <= 3 &&
          0 <= cnt && cnt <= 3 * s && cnt <= 3000000000 &&
          LuxuryBlockPrefix(x@pre, s, m, cnt) && emp
    */
    for (int m = 0; m < 3; m++)
        if (base + m * s <= x)
            cnt++;
    return cnt;
}

/* solver: complete interval case. */
static long long solver(long long l, long long r)
/* QCP_INSERT_BEGIN:shard09-P033-normalized-solver-contract */
/*@ Require
      1 <= l && l <= r && r <= 1000000000000000000 &&
      emp
    Ensure
      Spec(l, r, __return) && emp
*/
/* QCP_INSERT_END:shard09-P033-normalized-solver-contract */
{
    return count_upto(r) - count_upto(l - 1);
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         long long l, r;
//         scanf("%lld %lld", &l, &r);
//         printf("%lld\n", solver(l, r));
//     }
//     return 0;
// }
