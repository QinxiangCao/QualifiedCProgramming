// #include <stdio.h>
// #include <stdlib.h>
// #include <math.h>
// #include <stdint.h>
typedef unsigned long long u64;
typedef struct
{
    u64 d, p;
} Cand;
static u64 mulmod(u64 a, u64 b, u64 m)
{
    return (u64)((__uint128_t)a * b % m);
}
static u64 powmod(u64 a, u64 e, u64 m)
{
    u64 r = 1;
    for (; e; e >>= 1, a = mulmod(a, a, m))
        if (e & 1)
            r = mulmod(r, a, m);
    return r;
}
static int prime(u64 n)
{
    if (n < 2)
        return 0;
    static const int small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (int i = 0; i < 12; i++)
    {
        if (n == (u64)small[i])
            return 1;
        if (n % (u64)small[i] == 0)
            return 0;
    }
    u64 d = n - 1, s = 0;
    while (!(d & 1))
        d >>= 1, s++;
    static const u64 base[] = {2, 3, 5, 7, 11, 13};
    for (int i = 0; i < 6; i++)
    {
        u64 x = powmod(base[i] % n, d, n);
        if (x == 1 || x == n - 1)
            continue;
        int ok = 0;
        for (u64 j = 1; j < s; j++)
        {
            x = mulmod(x, x, n);
            if (x == n - 1)
            {
                ok = 1;
                break;
            }
        }
        if (!ok)
            return 0;
    }
    return 1;
}
static int power_eq(u64 a, int e, u64 q)
{
    __uint128_t r = 1;
    for (int i = 0; i < e; i++)
    {
        r *= a;
        if (r > q)
            return 0;
    }
    return r == q;
}
static u64 prime_power_base(u64 q)
{
    if (prime(q))
        return q;
    for (int e = 2; e <= 40; e++)
    {
        long double z = powl((long double)q, 1.0L / e);
        u64 a = (u64)z;
        for (u64 b = a > 2 ? a - 2 : 2; b <= a + 2; b++)
            if (prime(b) && power_eq(b, e, q))
                return b;
    }
    return 0;
}
static int cmpu(const void *A, const void *B)
{
    u64 a = *(const u64 *)A, b = *(const u64 *)B;
    return a < b ? -1 : a > b;
}
static Cand *cand;
static int cn;
static u64 used[64];
static int us;
static u64 dfs(u64 rem, int at)
{
    if (rem == 1)
        return 1;
    u64 ans = 0;
    for (int i = at; i < cn; i++)
        if (rem % cand[i].d == 0)
        {
            int ok = 1;
            for (int j = 0; j < us; j++)
                if (used[j] == cand[i].p)
                    ok = 0;
            if (ok)
            {
                used[us++] = cand[i].p;
                ans += dfs(rem / cand[i].d, i + 1);
                us--;
            }
        }
    return ans;
}
/* QCP_INSERT_BEGIN:P093_541D_super_j.support */
/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
      (UInt64Array::full_shape : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P093_541D_super_j_lib */
/* QCP_INSERT_END:P093_541D_super_j.support */
static u64 solver(u64 A) /* QCP_INSERT_BEGIN:P093_541D_super_j.contract */

/*@ With (a : Z)
    Require
      1 <= a && a <= 1000000000000 &&
      A == a &&
      UInt64Array::full_shape(used, 64)
    Ensure
      Spec(a, __return) &&
      UInt64Array::full_shape(used, 64)
*/
/* QCP_INSERT_END:P093_541D_super_j.contract */
{
    if (A == 1)
        return 1;
    u64 divs[10000];
    int dc = 0;
    for (u64 i = 1; i * i <= A; i++)
        if (A % i == 0)
        {
            divs[dc++] = i;
            if (i * i != A)
                divs[dc++] = A / i;
        }
    qsort(divs, dc, sizeof *divs, cmpu);
    cand = malloc((size_t)dc * sizeof *cand);
    cn = 0;
    us = 0;
    for (int i = 0; i < dc; i++)
        if (divs[i] > 1)
        {
            u64 p = prime_power_base(divs[i] - 1);
            if (p)
                cand[cn++] = (Cand){divs[i], p};
        }
    u64 answer = dfs(A, 0);
    free(cand);
    cand = NULL;
    return answer;
}
// int main(void)
// {
//     u64 A;
//     if (scanf("%llu", &A) != 1)
//         return 0;
//     printf("%llu\n", solver(A));
//     return 0;
// }
