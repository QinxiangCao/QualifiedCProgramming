/*
 * Codeforces 1750/F - Majority  (rating 2700, COMBINATORICS DP)
 *
 * A string is rated iff, reading left to right, each maximal block of ones can
 * swallow the next one: blocks of sizes p and q separated by z zeros merge iff
 * p + q >= z.  So let A[i] count the rated strings of length i and B[i][j] the
 * strings of length i whose greedily merged prefix stops at length j; then
 *   A[i] = 2^(i-1) - sum_{j<i} A[j] * W[i-j][j],
 * where W[d][j] counts the blocked tails of length d after a block of j.
 * Splitting W by whether the following block's own merged prefix is capped by
 * its length or by the gap turns it into a power of two plus Q[d-j-1], where
 * Q[D] sums the prefix counts over all splits L + t = D with t < L.  Q depends
 * only on D, so everything runs in O(n^2) with O(n) memory per row and only
 * additions and multiplications, which suits the arbitrary modulus.
 */

// #include <stdio.h>
// #include <stdlib.h>
/* QCP_INSERT_BEGIN:shard09-P093-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P093_1750F_majority_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P093-solver-support */

/* Pure closed form for pow2[k] == 2^k mod m; lets the loop invariants name
 * the value instead of inlining Z.pow. */
/*@ Extern Coq
      (Pow2Mod : Z -> Z -> Z)
      (SomeList : list Z -> list (option Z))
*/

/* Contents of the DP scratch arrays, as functions of (m, n) and the row
 * index. These let the loop invariants say what A / Q / Brow / P hold rather
 * than only that they are owned; without that, A[i] carries no meaning in
 * the logic and any semantic claim about it is unprovable. */
/*@ Extern Coq
      (Zeros : Z -> list Z)
      (SomeListUndefTail : list Z -> list (option Z))
      (DPA : Z -> Z -> Z -> list Z)
      (DPQ : Z -> Z -> Z -> list Z)
      (QPartial : Z -> Z -> Z -> Z -> list Z)
      (RowBrow : Z -> Z -> Z -> Z -> Z)
      (RowBlocked : Z -> Z -> Z -> Z -> Z)
      (RowP : Z -> Z -> Z -> Z -> Z)
      (RowRun : Z -> Z -> Z -> Z -> Z)
*/

/* QCP_INSERT_BEGIN:shard09-P093-alloc-contracts */
void *malloc(unsigned long size)
/*@ With (count : Z)
    Require
      0 <= count && size == count * 8 &&
      emp
    Ensure
      Int64Array::undef_full(__return, count)
*/;

void free(void *ptr)
/*@ With (count : Z) (cells : list (option Z))
    Require
      0 <= count && Zlength(cells) == count &&
      Int64Array::mixed_full(ptr, count, cells)
    Ensure
      emp
*/;
/* QCP_INSERT_END:shard09-P093-alloc-contracts */

/* solver: number of rated strings of length n, modulo m. */
static long long solver(int n, long long m)
/* QCP_INSERT_BEGIN:shard09-P093-solver-contract */
/*@
    Require
      1 <= n && n <= 5000 && 10 <= m && m <= 1000000000 &&
      emp
    Ensure
      Spec(n, m, __return) &&
      emp
*/
/* QCP_INSERT_END:shard09-P093-solver-contract */
{
    long long *A = malloc((unsigned long)(n + 2) * sizeof(long long)) /*@ where count = n + 2 */;
    long long *Q = malloc((unsigned long)(2 * n + 4) * sizeof(long long)) /*@ where count = 2 * n + 4 */;
    long long *pow2 = malloc((unsigned long)(n + 2) * sizeof(long long)) /*@ where count = n + 2 */;
    long long *Brow = malloc((unsigned long)(n + 2) * sizeof(long long)) /*@ where count = n + 2 */;
    long long *P = malloc((unsigned long)(n + 2) * sizeof(long long)) /*@ where count = n + 2 */;

    int i;
    /*@ Inv Assert
        exists lA lBrow lP,
          n == n@pre && m == m@pre &&
          1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
          0 <= i && i <= n@pre + 2 &&
          Zlength(lA) == i && Zlength(lBrow) == i && Zlength(lP) == i &&
          lA == Zeros(i) && lBrow == Zeros(i) && lP == Zeros(i) &&
          Int64Array::full(A, i, lA) * Int64Array::undef_seg(A, i, n@pre + 2) *
          Int64Array::full(Brow, i, lBrow) * Int64Array::undef_seg(Brow, i, n@pre + 2) *
          Int64Array::full(P, i, lP) * Int64Array::undef_seg(P, i, n@pre + 2) *
          Int64Array::undef_full(Q, 2 * n@pre + 4) *
          Int64Array::undef_full(pow2, n@pre + 2)
     */
    for (i = 0; i < n + 2; i++) {       /* malloc does not zero: Q is read
                                             * before it is written, and A[j]
                                             * for j > i must read as 0 */
        A[i] = 0;
        Brow[i] = 0;
        P[i] = 0;
    }
    /*@ Inv Assert
        exists lA lBrow lP lQ,
          n == n@pre && m == m@pre &&
          1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
          0 <= i && i <= 2 * n@pre + 4 &&
          Zlength(lA) == n@pre + 2 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
          lA == Zeros(n@pre + 2) && lBrow == Zeros(n@pre + 2) && lP == Zeros(n@pre + 2) &&
          Zlength(lQ) == i && lQ == Zeros(i) &&
          Int64Array::full(A, n@pre + 2, lA) * Int64Array::full(Brow, n@pre + 2, lBrow) *
          Int64Array::full(P, n@pre + 2, lP) *
          Int64Array::full(Q, i, lQ) * Int64Array::undef_seg(Q, i, 2 * n@pre + 4) *
          Int64Array::undef_full(pow2, n@pre + 2)
     */
    for (i = 0; i < 2 * n + 4; i++)
        Q[i] = 0;
    pow2[0] = 1 % m;
    /*@ Inv Assert
        exists lA lBrow lP lQ lpow2,
          n == n@pre && m == m@pre &&
          1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
          1 <= i && i <= n@pre + 1 &&
          Zlength(lA) == n@pre + 2 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
          lA == Zeros(n@pre + 2) && lBrow == Zeros(n@pre + 2) && lP == Zeros(n@pre + 2) &&
          Zlength(lQ) == 2 * n@pre + 4 && lQ == Zeros(2 * n@pre + 4) &&
          Zlength(lpow2) == i &&
          (forall k, (0 <= k && k < i) => Znth(k, lpow2, 0) == Pow2Mod(k, m@pre)) &&
          Int64Array::full(A, n@pre + 2, lA) * Int64Array::full(Brow, n@pre + 2, lBrow) *
          Int64Array::full(P, n@pre + 2, lP) * Int64Array::full(Q, 2 * n@pre + 4, lQ) *
          Int64Array::full(pow2, i, lpow2) * Int64Array::undef_seg(pow2, i, n@pre + 2)
     */
    for (i = 1; i <= n; i++)
        pow2[i] = pow2[i - 1] * 2 % m;

    /*@ Inv Assert
        exists lA lpow2 lQ lBrow lP,
          n == n@pre && m == m@pre &&
          1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
          1 <= i && i <= n@pre + 1 &&
          Zlength(lA) == n@pre + 2 && Zlength(lpow2) == n@pre + 1 &&
          Zlength(lQ) == 2 * n@pre + 4 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
          (forall k, (0 <= k && k < n@pre + 1) => Znth(k, lpow2, 0) == Pow2Mod(k, m@pre)) &&
          lA == DPA(m@pre, n@pre, i - 1) &&
          lQ == DPQ(m@pre, n@pre, i - 1) &&
          Int64Array::full(A, n@pre + 2, lA) *
              Int64Array::full(pow2, n@pre + 1, lpow2) *
              Int64Array::undef_seg(pow2, n@pre + 1, n@pre + 2) *
          Int64Array::full(Q, 2 * n@pre + 4, lQ) *
          Int64Array::full(Brow, n@pre + 2, lBrow) * Int64Array::full(P, n@pre + 2, lP)
     */
    for (i = 1; i <= n; i++) {
        long long blocked = 0;
        /*@ Inv Assert
            exists lA lpow2 lQ lBrow lP,
              n == n@pre && m == m@pre &&
              1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
              1 <= i && i <= n@pre &&
              1 <= j && j <= i &&
              0 <= blocked && blocked < m@pre &&
              Zlength(lA) == n@pre + 2 && Zlength(lpow2) == n@pre + 1 &&
              Zlength(lQ) == 2 * n@pre + 4 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
              (forall k, (0 <= k && k < n@pre + 1) => Znth(k, lpow2, 0) == Pow2Mod(k, m@pre)) &&
              lA == DPA(m@pre, n@pre, i - 1) &&
              lQ == DPQ(m@pre, n@pre, i - 1) &&
              blocked == RowBlocked(m@pre, n@pre, i, j - 1) &&
              (forall jj, (1 <= jj && jj < j) =>
                 Znth(jj, lBrow, 0) == RowBrow(m@pre, n@pre, i, jj)) &&
              Int64Array::full(A, n@pre + 2, lA) *
              Int64Array::full(pow2, n@pre + 1, lpow2) *
              Int64Array::undef_seg(pow2, n@pre + 1, n@pre + 2) *
              Int64Array::full(Q, 2 * n@pre + 4, lQ) *
              Int64Array::full(Brow, n@pre + 2, lBrow) * Int64Array::full(P, n@pre + 2, lP)
         */
        for (int j = 1; j < i; j++) {
            int d = i - j;
            /* W[d][j] = 1 (all-zero tail)
             *         + (2^Lmax - 1) for the gaps wide enough to cap the next
             *           block by its own length
             *         + Q[d-j-1] for the rest */
            long long w = 1 % m;
            int z0 = (d + j + 2) / 2;     /* ceil((d+j+1)/2) */
            int Lmax = d - z0;
            if (Lmax >= 1) {
                /*@ 0 <= Lmax && Lmax < n@pre + 1 by local */
                w = (w + pow2[Lmax] - 1 % m + m) % m;
            }
            int D = d - j - 1;
            if (D >= 0) {
                /*@ 0 <= D && D < 2 * n@pre + 4 by local */
                w = (w + Q[D]) % m;
            }
            Brow[j] = A[j] * w % m;
            blocked = (blocked + Brow[j]) % m;
        }
        A[i] = ((pow2[i - 1] - blocked) % m + m) % m;

        /*@ Assert
            exists lA lpow2 lQ lBrow lP,
              n == n@pre && m == m@pre &&
              1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
              1 <= i && i <= n@pre &&
              0 <= blocked && blocked < m@pre &&
              Zlength(lA) == n@pre + 2 && Zlength(lpow2) == n@pre + 1 &&
              Zlength(lQ) == 2 * n@pre + 4 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
              (forall k, (0 <= k && k < n@pre + 1) => Znth(k, lpow2, 0) == Pow2Mod(k, m@pre)) &&
              lA == DPA(m@pre, n@pre, i) &&
              lQ == DPQ(m@pre, n@pre, i - 1) &&
              blocked == RowBlocked(m@pre, n@pre, i, i - 1) &&
              (forall jj, (1 <= jj && jj < i) =>
                 Znth(jj, lBrow, 0) == RowBrow(m@pre, n@pre, i, jj)) &&
              Int64Array::full(A, n@pre + 2, lA) *
              Int64Array::full(pow2, n@pre + 1, lpow2) *
              Int64Array::undef_seg(pow2, n@pre + 1, n@pre + 2) *
              Int64Array::full(Q, 2 * n@pre + 4, lQ) *
              Int64Array::full(Brow, n@pre + 2, lBrow) * Int64Array::full(P, n@pre + 2, lP)
         */

        /* row of "maximal merged prefix = q" counts, then its prefix sums */
        long long run = 0;
        /*@ Inv Assert
            exists lA lpow2 lQ lBrow lP,
              n == n@pre && m == m@pre &&
              1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
              1 <= i && i <= n@pre &&
              0 <= q && q <= i + 1 &&
              0 <= blocked && blocked < m@pre &&
              0 <= run && run < m@pre &&
              Zlength(lA) == n@pre + 2 && Zlength(lpow2) == n@pre + 1 &&
              Zlength(lQ) == 2 * n@pre + 4 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
              (forall k, (0 <= k && k < n@pre + 1) => Znth(k, lpow2, 0) == Pow2Mod(k, m@pre)) &&
              lA == DPA(m@pre, n@pre, i) &&
              lQ == DPQ(m@pre, n@pre, i - 1) &&
              blocked == RowBlocked(m@pre, n@pre, i, i - 1) &&
              run == RowRun(m@pre, n@pre, i, q) &&
              (forall jj, (1 <= jj && jj < i) =>
                 Znth(jj, lBrow, 0) == RowBrow(m@pre, n@pre, i, jj)) &&
              (forall qq, (0 <= qq && qq < q) =>
                 Znth(qq, lP, 0) == RowP(m@pre, n@pre, i, qq)) &&
              Int64Array::full(A, n@pre + 2, lA) *
              Int64Array::full(pow2, n@pre + 1, lpow2) *
              Int64Array::undef_seg(pow2, n@pre + 1, n@pre + 2) *
              Int64Array::full(Q, 2 * n@pre + 4, lQ) *
              Int64Array::full(Brow, n@pre + 2, lBrow) * Int64Array::full(P, n@pre + 2, lP)
         */
        for (int q = 0; q <= i; q++) {
            long long c = (q == 0) ? 0 : (q < i ? Brow[q] : A[i]);
            run = (run + c) % m;
            P[q] = run;
        }
        /*@ Inv Assert
            exists lA lpow2 lQ lBrow lP,
              n == n@pre && m == m@pre &&
              1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
              1 <= i && i <= n@pre &&
              0 <= t && t <= i &&
              0 <= blocked && blocked < m@pre &&
              0 <= run && run < m@pre &&
              Zlength(lA) == n@pre + 2 && Zlength(lpow2) == n@pre + 1 &&
              Zlength(lQ) == 2 * n@pre + 4 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
              (forall k, (0 <= k && k < n@pre + 1) => Znth(k, lpow2, 0) == Pow2Mod(k, m@pre)) &&
              lA == DPA(m@pre, n@pre, i) &&
              lQ == QPartial(m@pre, n@pre, i, t) &&
              blocked == RowBlocked(m@pre, n@pre, i, i - 1) &&
              run == RowRun(m@pre, n@pre, i, i + 1) &&
              (forall qq, (0 <= qq && qq <= i) =>
                 Znth(qq, lP, 0) == RowP(m@pre, n@pre, i, qq)) &&
              Int64Array::full(A, n@pre + 2, lA) *
              Int64Array::full(pow2, n@pre + 1, lpow2) *
              Int64Array::undef_seg(pow2, n@pre + 1, n@pre + 2) *
              Int64Array::full(Q, 2 * n@pre + 4, lQ) *
              Int64Array::full(Brow, n@pre + 2, lBrow) * Int64Array::full(P, n@pre + 2, lP)
         */
        for (int t = 0; t < i; t++)       /* feed Q[L+t] for t < L = i */
            if (i + t <= 2 * n)
                Q[i + t] = (Q[i + t] + P[t]) % m;

        /*@ Assert
            exists lA lpow2 lQ lBrow lP,
              n == n@pre && m == m@pre &&
              1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
              1 <= i && i <= n@pre &&
              0 <= blocked && blocked < m@pre &&
              0 <= run && run < m@pre &&
              Zlength(lA) == n@pre + 2 && Zlength(lpow2) == n@pre + 1 &&
              Zlength(lQ) == 2 * n@pre + 4 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
              (forall k, (0 <= k && k < n@pre + 1) => Znth(k, lpow2, 0) == Pow2Mod(k, m@pre)) &&
              lA == DPA(m@pre, n@pre, i) &&
              lQ == DPQ(m@pre, n@pre, i) &&
              Int64Array::full(A, n@pre + 2, lA) *
              Int64Array::full(pow2, n@pre + 1, lpow2) *
              Int64Array::undef_seg(pow2, n@pre + 1, n@pre + 2) *
              Int64Array::full(Q, 2 * n@pre + 4, lQ) *
              Int64Array::full(Brow, n@pre + 2, lBrow) * Int64Array::full(P, n@pre + 2, lP)
         */
    }
    long long ans = A[n];
    /*@ Assert
        exists lA lQ lpow2 lBrow lP cA cQ cpow2 cBrow cP,
          n == n@pre && m == m@pre && i == n@pre + 1 &&
          1 <= n@pre && n@pre <= 5000 && 10 <= m@pre && m@pre <= 1000000000 &&
          Zlength(lA) == n@pre + 2 && Zlength(lQ) == 2 * n@pre + 4 &&
          Zlength(lpow2) == n@pre + 1 && Zlength(lBrow) == n@pre + 2 && Zlength(lP) == n@pre + 2 &&
          lA == DPA(m@pre, n@pre, n@pre) &&
          ans == Znth(n@pre, lA, 0) &&
          Spec(n@pre, m@pre, ans) &&
          cA == SomeList(lA) && cQ == SomeList(lQ) && cpow2 == SomeListUndefTail(lpow2) &&
          cBrow == SomeList(lBrow) && cP == SomeList(lP) &&
          Zlength(cA) == n@pre + 2 && Zlength(cQ) == 2 * n@pre + 4 &&
          Zlength(cpow2) == n@pre + 2 && Zlength(cBrow) == n@pre + 2 && Zlength(cP) == n@pre + 2 &&
          Int64Array::mixed_full(A, Zlength(cA), cA) *
          Int64Array::mixed_full(Q, Zlength(cQ), cQ) *
          Int64Array::mixed_full(pow2, Zlength(cpow2), cpow2) *
          Int64Array::mixed_full(Brow, Zlength(cBrow), cBrow) *
          Int64Array::mixed_full(P, Zlength(cP), cP)
     */
    free(A); free(Q); free(pow2); free(Brow); free(P);
    return ans;

}

// int main(void)
// {
//     int n;
//     long long m;
//     if (scanf("%d %lld", &n, &m) != 2)
//         return 0;
//     printf("%lld\n", solver(n, m));
//     return 0;
// }
