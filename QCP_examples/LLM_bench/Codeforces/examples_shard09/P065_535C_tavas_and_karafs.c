/*
 * Codeforces 535/C - Tavas and Karafs  (rating 1900, BINARY SEARCH)
 *
 * The prefix l..r can be eaten in t m-bite moves iff the tallest karafs fits
 * (s_r <= t) and the total height fits (sum <= t*m).  Both conditions get
 * harder as r grows, so binary search the largest feasible r.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P065-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P065_535C_tavas_and_karafs_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Spec : Z -> Z -> list(Z * Z * Z) -> list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P065-solver-support */

/*@ Extern Coq
      (QueryAnswer : Z -> Z -> (Z * Z * Z) -> Z -> Prop)
*/
/*@ Extern Coq
      (pair : {A B} -> A -> B -> A * B)
*/

/* height: s_i = A + (i-1)*B. */
static long long height(long long A, long long B, long long i)
/*@ Require
      1 <= A && A <= 1000000 &&
      1 <= B && B <= 1000000 &&
      1 <= i && i <= 2000000 && emp
    Ensure
      __return == A@pre + (i@pre - 1) * B@pre && emp
*/
{
    return A + (i - 1) * B;
}

/* range_sum: sum of s_l .. s_r (arithmetic progression). */
static long long range_sum(long long A, long long B, long long l, long long r)
/*@ Require
      1 <= A && A <= 1000000 &&
      1 <= B && B <= 1000000 &&
      1 <= l && l <= r && r <= 2000000 && emp
    Ensure
      __return ==
        (A@pre + (l@pre - 1) * B@pre +
         A@pre + (r@pre - 1) * B@pre) *
        (r@pre - l@pre + 1) / 2 && emp
*/
{
    long long cnt = r - l + 1;
    return (height(A, B, l) + height(A, B, r)) * cnt / 2;
}

/* solver: pure.  Largest r with l <= r that can be eaten, or -1. */
static long long answer_query(long long A, long long B, long long l,
                              long long t, long long m)
/*@ Require
      1 <= A && A <= 1000000 &&
      1 <= B && B <= 1000000 &&
      1 <= l && l <= 1000000 &&
      1 <= t && t <= 1000000 &&
      1 <= m && m <= 1000000 && emp
    Ensure
      -1 <= __return && __return <= 2000000 &&
      QueryAnswer(A@pre, B@pre, pair(pair(l@pre, t@pre), m@pre), __return) && emp
*/
{
    if (height(A, B, l) > t)
        return -1;
    long long lo = l, hi = l;
    /*@ Inv Assert
          exists ans,
          A == A@pre && B == B@pre && l == l@pre && lo == l@pre &&
          t == t@pre && m == m@pre &&
          1 <= A@pre && A@pre <= 1000000 &&
          1 <= B@pre && B@pre <= 1000000 &&
          1 <= l@pre && l@pre <= 1000000 &&
          1 <= t@pre && t@pre <= 1000000 &&
          1 <= m@pre && m@pre <= 1000000 &&
          l@pre <= hi && hi <= 2000000 &&
          l@pre <= ans && ans <= 2000000 &&
          QueryAnswer(A@pre, B@pre, pair(pair(l@pre, t@pre), m@pre), ans) && emp
    */
    while (height(A, B, hi) <= t)         /* find an upper bound first */
        hi *= 2;
    /*@ Assert
          exists ans,
          A == A@pre && B == B@pre && l == l@pre &&
          t == t@pre && m == m@pre &&
          1 <= A@pre && A@pre <= 1000000 &&
          1 <= B@pre && B@pre <= 1000000 &&
          1 <= l@pre && l@pre <= 1000000 &&
          1 <= t@pre && t@pre <= 1000000 &&
          1 <= m@pre && m@pre <= 1000000 &&
          l@pre <= lo && lo <= ans && ans <= hi && hi <= 2000000 &&
          QueryAnswer(A@pre, B@pre, pair(pair(l@pre, t@pre), m@pre), ans) && emp
    */
    /*@ Inv Assert
          exists ans,
          A == A@pre && B == B@pre && l == l@pre &&
          t == t@pre && m == m@pre &&
          1 <= A@pre && A@pre <= 1000000 &&
          1 <= B@pre && B@pre <= 1000000 &&
          1 <= l@pre && l@pre <= 1000000 &&
          1 <= t@pre && t@pre <= 1000000 &&
          1 <= m@pre && m@pre <= 1000000 &&
          l@pre <= lo && lo <= ans && ans <= hi && hi <= 2000000 &&
          QueryAnswer(A@pre, B@pre, pair(pair(l@pre, t@pre), m@pre), ans) && emp
    */
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;
        if (height(A, B, mid) <= t && range_sum(A, B, l, mid) <= t * m)
            lo = mid;
        else
            hi = mid - 1;
    }
    return lo;
}

/* solver: complete case.  Answer the entire logical query list. */
static void solver(long long A, long long B, const long long *ql,
                   const long long *qt, const long long *qm, int n,
                   long long *out)
/* QCP_INSERT_BEGIN:shard09-P065-normalized-solver-contract */
/*@ With (queries : list(Z*Z*Z)) (left_limits : list Z) (times : list Z) (maxima : list Z)
    Require
      1 <= A && A <= 1000000 && 1 <= B && B <= 1000000 &&
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (1 <= fst(fst(queries[i])) && fst(fst(queries[i])) <= 1000000 && 1 <= snd(fst(queries[i])) && snd(fst(queries[i])) <= 1000000 && 1 <= snd(queries[i]) && snd(queries[i]) <= 1000000)) && n == Zlength(queries) && Zlength(left_limits) == n && Zlength(times) == n && Zlength(maxima) == n && (forall i, (0 <= i && i < n) => (left_limits[i] == fst(fst(queries[i])) && times[i] == snd(fst(queries[i])) && maxima[i] == snd(queries[i]))) && Int64Array::full(ql, n, left_limits) * Int64Array::full(qt, n, times) * Int64Array::full(qm, n, maxima) * Int64Array::full_shape(out, n)
    Ensure
      exists (result : list Z), Spec(A, B, queries, result) && Int64Array::full(ql, n, left_limits) * Int64Array::full(qt, n, times) * Int64Array::full(qm, n, maxima) * Int64Array::full(out, n, result)
*/
/* QCP_INSERT_END:shard09-P065-normalized-solver-contract */
{
    /*@ Inv Assert
          exists result,
          A == A@pre && B == B@pre && ql == ql@pre &&
          qt == qt@pre && qm == qm@pre && out == out@pre && n == n@pre &&
          1 <= A@pre && A@pre <= 1000000 &&
          1 <= B@pre && B@pre <= 1000000 &&
          1 <= n@pre && n@pre <= 100000 &&
          n@pre == Zlength(queries) &&
          Zlength(left_limits) == n@pre &&
          Zlength(times) == n@pre &&
          Zlength(maxima) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (1 <= fst(fst(queries[k])) && fst(fst(queries[k])) <= 1000000 &&
             1 <= snd(fst(queries[k])) && snd(fst(queries[k])) <= 1000000 &&
             1 <= snd(queries[k]) && snd(queries[k]) <= 1000000)) &&
          (forall k, (0 <= k && k < n@pre) =>
            (left_limits[k] == fst(fst(queries[k])) &&
             times[k] == snd(fst(queries[k])) &&
             maxima[k] == snd(queries[k]))) &&
          0 <= i && i <= n@pre &&
          Zlength(result) == i &&
          (forall k, (0 <= k && k < i) =>
            QueryAnswer(A@pre, B@pre, queries[k], result[k])) &&
          Int64Array::full(ql@pre, n@pre, left_limits) *
          Int64Array::full(qt@pre, n@pre, times) *
          Int64Array::full(qm@pre, n@pre, maxima) *
          Int64Array::seg(out@pre, 0, i, result) *
          Int64Array::undef_seg(out@pre, i, n@pre)
    */
    for (int i = 0; i < n; i++)
        out[i] = answer_query(A, B, ql[i], qt[i], qm[i]);
}

// int main(void)
// {
//     long long A, B;
//     int n;
//     if (scanf("%lld %lld %d", &A, &B, &n) != 3)
//         return 0;
//     static long long ql[100005], qt[100005], qm[100005], out[100005];
//     for (int i = 0; i < n; i++)
//         scanf("%lld %lld %lld", &ql[i], &qt[i], &qm[i]);
//     solver(A, B, ql, qt, qm, n, out);
//     for (int i = 0; i < n; i++)
//         printf("%lld\n", out[i]);
//     return 0;
// }
