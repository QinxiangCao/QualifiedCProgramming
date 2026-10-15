/* Codeforces 1989/E - Distance to Different */
// #include <stdio.h>
// #include <stdlib.h>
typedef unsigned long size_t;
void *calloc(size_t nmemb, size_t size)
/*@ Require 0 <= nmemb && size == sizeof(long long)
    Ensure __return != 0 &&
           Int64Array::full(__return, nmemb, repeat_Z(0, nmemb))
*/;
void free(void *ptr)
/*@ Require exists values cap, Int64Array::full(ptr, cap, values)
    Ensure emp
*/;
#define MOD 998244353LL
#define AT(a, i, j) (a)[(size_t)(i) * W + (j)]
/* QCP_INSERT_BEGIN:P082_1989E_distance_to_different.support */
/*@ Extern Coq
      (Zmin : Z -> Z -> Z)
      (Spec : Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P082_1989E_distance_to_different_lib */
/*@ Extern Coq
      (P082InitState : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082ColumnsState : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082ColumnProgress : Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082FinalValue : Z -> Z -> list Z -> Z -> Prop)
*/
/*@ Extern Coq
      (P082SemanticInit : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082SemanticColumns : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (P082SemanticProgress : Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
*/
/* QCP_INSERT_END:P082_1989E_distance_to_different.support */
static long long solver(int n,
                        int k) /* QCP_INSERT_BEGIN:P082_1989E_distance_to_different.contract */

/*@
    Require
      2 <= n && n <= 200000 &&
      2 <= k && k <= Zmin(n, 10)
    Ensure
      Spec(n, k, __return)
*/
/* QCP_INSERT_END:P082_1989E_distance_to_different.contract */
{
    int W = k + 1;
    long long *dp = calloc((size_t)(n + 1) * W, sizeof(*dp)),
              *pref = calloc((size_t)(n + 1) * W, sizeof(*pref));
    /*@ Inv Assert exists dl pl,
        n == n@pre && k == k@pre && W == k + 1 &&
        2 <= n && n <= 200000 && 2 <= k && k <= Zmin(n, 10) &&
        0 <= (n + 1) * W && (n + 1) * W <= UINT_MAX &&
        1 <= i && i <= n + 1 &&
        P082InitState(n, k, i, dl, pl) &&
        P082SemanticInit(n, k, i, dl, pl) &&
        Int64Array::full(dp, (n + 1) * W, dl) *
        Int64Array::full(pref, (n + 1) * W, pl)
    */
    for (int i = 1; i <= n; ++i)
    {
        /*@ 0 <= i * W + 1 && i * W + 1 < (n + 1) * W &&
            0 <= (i - 1) * W + 1 && (i - 1) * W + 1 < (n + 1) * W
            by local */
        AT(dp, i, 1) = 1;
        AT(pref, i, 1) = (AT(pref, i - 1, 1) + 1) % MOD;
    }
    /*@ Inv Assert exists dl pl,
        n == n@pre && k == k@pre && W == k + 1 &&
        2 <= n && n <= 200000 && 2 <= k && k <= Zmin(n, 10) &&
        0 <= (n + 1) * W && (n + 1) * W <= UINT_MAX &&
        2 <= j && j <= k + 1 &&
        P082ColumnsState(n, k, j, dl, pl) &&
        P082SemanticColumns(n, k, j, dl, pl) &&
        Int64Array::full(dp, (n + 1) * W, dl) *
        Int64Array::full(pref, (n + 1) * W, pl)
    */
    for (int j = 2; j <= k; ++j)
    {
        /*@ Inv Assert exists dl pl,
            n == n@pre && k == k@pre && W == k + 1 &&
            2 <= n && n <= 200000 && 2 <= k && k <= Zmin(n, 10) &&
            0 <= (n + 1) * W && (n + 1) * W <= UINT_MAX &&
            2 <= j && j <= k && 1 <= i && i <= n + 1 &&
            P082ColumnProgress(n, k, j, i, dl, pl) &&
            P082SemanticProgress(n, k, j, i, dl, pl) &&
            Int64Array::full(dp, (n + 1) * W, dl) *
            Int64Array::full(pref, (n + 1) * W, pl)
        */
        for (int i = 1; i <= n; ++i)
        {
            /*@ 0 <= (i - 1) * W + (j - 1) &&
                (i - 1) * W + (j - 1) < (n + 1) * W by local */
            long long val = AT(pref, i - 1, j - 1);
            if (i >= 3)
            {
                /*@ 0 <= (i - 2) * W + (j - 1) &&
                    (i - 2) * W + (j - 1) < (n + 1) * W by local */
                val -= AT(dp, i - 2, j - 1);
            }
            if (j == k)
            {
                /*@ 0 <= (i - 1) * W + k &&
                    (i - 1) * W + k < (n + 1) * W by local */
                val += AT(pref, i - 1, k);
                if (i >= 3)
                {
                    /*@ 0 <= (i - 2) * W + k &&
                        (i - 2) * W + k < (n + 1) * W by local */
                    val -= AT(dp, i - 2, k);
                }
            }
            /*@ 0 <= i * W + j && i * W + j < (n + 1) * W by local */
            AT(dp, i, j) = (val % MOD + MOD) % MOD;
            /*@ 0 <= (i - 1) * W + j &&
                (i - 1) * W + j < (n + 1) * W by local */
            AT(pref, i, j) = (AT(pref, i - 1, j) + AT(dp, i, j)) % MOD;
        }
    }
    /*@ 0 <= n * W + k && n * W + k < (n + 1) * W by local */
    long long ans = AT(dp, n, k);
    if (n >= 2)
    {
        /*@ 0 <= (n - 2) * W + (k - 1) &&
            (n - 2) * W + (k - 1) < (n + 1) * W &&
            0 <= (n - 2) * W + k &&
            (n - 2) * W + k < (n + 1) * W by local */
        ans = (ans + AT(dp, n - 2, k - 1) + AT(dp, n - 2, k)) % MOD;
    }
    /*@ Assert exists dl pl,
        n == n@pre && k == k@pre && W == k + 1 &&
        P082FinalValue(n, k, dl, ans) &&
        Int64Array::full(dp, (n + 1) * W, dl) *
        Int64Array::full(pref, (n + 1) * W, pl)
    */
    free(dp);
    free(pref);
    return ans;
}
// int main(void)
// {
//     int n, k;
//     if (scanf("%d %d", &n, &k) != 2)
//         return 0;
//     printf("%lld\n", solver(n, k));
//     return 0;
// }
