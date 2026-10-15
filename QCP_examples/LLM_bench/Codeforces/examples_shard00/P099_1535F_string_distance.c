// #include <stdio.h>
// #include <stdlib.h>
#include "string.h"
#include "array2_ext_def.h"
// #include <stdint.h>
typedef uint64_t u64;
static char *strs, *sigs;
static int L, *idx, *bad;
static u64 *pref, *pw, *psum;
static int cmpidx(const void *A, const void *B)
{
    int a = *(const int *)A, b = *(const int *)B;
    int c = strcmp(sigs + (size_t)a * (L + 1), sigs + (size_t)b * (L + 1));
    return c ? c : a - b;
}
static int cmp64(const void *A, const void *B)
{
    u64 a = *(const u64 *)A, b = *(const u64 *)B;
    return a < b ? -1 : a > b;
}
static int has(u64 *a, int n, u64 x)
{
    int l = 0, r = n;
    while (l < r)
    {
        int m = (l + r) / 2;
        if (a[m] < x)
            l = m + 1;
        else
            r = m;
    }
    return l < n && a[l] == x;
}
static u64 subhash(int id, int l, int r)
{
    u64 *p = pref + (size_t)id * (L + 1);
    return p[r] - p[l];
}
static int one_pair(int a, int b)
{
    int lo = 0, hi = L;
    while (lo < hi)
    {
        int md = (lo + hi + 1) / 2;
        if (subhash(a, 0, md) == subhash(b, 0, md))
            lo = md;
        else
            hi = md - 1;
    }
    int l = lo;
    if (l == L)
        return 0;
    lo = 0;
    hi = L - l;
    while (lo < hi)
    {
        int md = (lo + hi + 1) / 2;
        if (subhash(a, L - md, L) == subhash(b, L - md, L))
            lo = md;
        else
            hi = md - 1;
    }
    int r = L - 1 - lo,
        sm = (strs[(size_t)a * (L + 1) + l] < strs[(size_t)b * (L + 1) + l]) ? a : b;
    int *bp = bad + (size_t)sm * (L + 1);
    return bp[r] - bp[l] == 0;
}
/* QCP_INSERT_BEGIN:P099_1535F_string_distance.support */
/*@ Extern Coq
      (Pre : list (list Z) -> Prop)
      (Spec : list (list Z) -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P099_1535F_string_distance_lib */
/* QCP_INSERT_END:P099_1535F_string_distance.support */
static long long
solver(int n, int length,
       const char *input) /* QCP_INSERT_BEGIN:P099_1535F_string_distance.contract */

/*@ With (strings : list (list Z))
             (storage_rows : list (list Z))
    Require
      1 <= Zlength(strings) && Zlength(strings) <= 200000 &&
      n == Zlength(strings) &&
      (forall i, (0 <= i && i < n) => Zlength(strings[i]) == length) &&
      Zlength(storage_rows) == n &&
      (forall i, (0 <= i && i < n) =>
        Zlength(Znth(i, storage_rows, nil)) == length + 1) &&
      (forall i j, (0 <= i && i < n && 0 <= j && j < length) =>
        (97 <= Znth(j, Znth(i, strings, nil), 0) &&
         Znth(j, Znth(i, strings, nil), 0) <= 122 &&
         Znth(j, Znth(i, storage_rows, nil), 0) ==
           Znth(j, Znth(i, strings, nil), 0))) &&
      (forall i, (0 <= i && i < n) =>
        Znth(length, Znth(i, storage_rows, nil), 0) == 0) &&
      Pre(strings) &&
      CharArray2::full(input, n, length + 1, storage_rows)
    Ensure
      Spec(strings, __return) &&
      CharArray2::full(input, n, length + 1, storage_rows)
*/
/* QCP_INSERT_END:P099_1535F_string_distance.contract */
{
    L = length;
    strs = malloc((size_t)n * (L + 1));
    sigs = malloc((size_t)n * (L + 1));
    for (int i = 0; i < n; i++)
        memcpy(strs + (size_t)i * (L + 1), input + (size_t)i * (L + 1), (size_t)L + 1);
    idx = malloc(n * sizeof *idx);
    bad = calloc((size_t)n * (L + 1), sizeof *bad);
    pref = calloc((size_t)n * (L + 1), sizeof *pref);
    pw = malloc((size_t)(L + 1) * sizeof *pw);
    psum = malloc((size_t)(L + 1) * sizeof *psum);
    pw[0] = 1;
    psum[0] = 0;
    const u64 P = 1000003ULL;
    for (int i = 0; i < L; i++)
    {
        pw[i + 1] = pw[i] * P;
        psum[i + 1] = psum[i] + pw[i];
    }
    for (int id = 0; id < n; id++)
    {
        idx[id] = id;
        char *s = strs + (size_t)id * (L + 1), *sg = sigs + (size_t)id * (L + 1);
        int cnt[26] = {0};
        u64 *hp = pref + (size_t)id * (L + 1);
        int *bp = bad + (size_t)id * (L + 1);
        for (int i = 0; i < L; i++)
        {
            cnt[s[i] - 'a']++;
            hp[i + 1] = hp[i] + (u64)(s[i] - 'a' + 1) * pw[i];
            if (i + 1 < L)
                bp[i + 1] = bp[i] + (s[i] > s[i + 1]);
            else
                bp[i + 1] = bp[i];
        }
        int z = 0;
        for (int c = 0; c < 26; c++)
            while (cnt[c]--)
                sg[z++] = (char)('a' + c);
        sg[z] = '\0';
    }
    qsort(idx, n, sizeof *idx, cmpidx);
    long long all = (long long)n * (n - 1) / 2, within = 0, ones = 0;
    for (int gl = 0; gl < n;)
    {
        int gr = gl + 1;
        while (gr < n &&
               !strcmp(sigs + (size_t)idx[gl] * (L + 1), sigs + (size_t)idx[gr] * (L + 1)))
            gr++;
        int g = gr - gl;
        within += (long long)g * (g - 1) / 2;
        if (g > 1)
        {
            long double paircost = (long double)g * g * 20.0L,
                        enumcost = (long double)g * L * L * (L < 26 ? L : 26);
            if (paircost <= enumcost)
            {
                for (int i = gl; i < gr; i++)
                    for (int j = i + 1; j < gr; j++)
                        ones += one_pair(idx[i], idx[j]);
            }
            else
            {
                u64 *orig = malloc((size_t)g * sizeof *orig);
                for (int i = 0; i < g; i++)
                    orig[i] = pref[(size_t)idx[gl + i] * (L + 1) + L];
                qsort(orig, g, sizeof *orig, cmp64);
                for (int ii = gl; ii < gr; ii++)
                {
                    int id = idx[ii];
                    char *s = strs + (size_t)id * (L + 1);
                    u64 base = pref[(size_t)id * (L + 1) + L];
                    for (int l = 0; l < L; l++)
                    {
                        int cnt[26] = {0}, mn = 26, mx = -1;
                        for (int r = l; r < L; r++)
                        {
                            int ch = s[r] - 'a';
                            cnt[ch]++;
                            if (ch < mn)
                                mn = ch;
                            if (ch > mx)
                                mx = ch;
                            if (mn >= s[l] - 'a' || mx <= s[r] - 'a')
                                continue;
                            u64 sh = 0;
                            int off = 0;
                            for (int c = 0; c < 26; c++)
                                if (cnt[c])
                                {
                                    sh += (u64)(c + 1) * pw[l + off] * psum[cnt[c]];
                                    off += cnt[c];
                                }
                            u64 nh = base - subhash(id, l, r + 1) + sh;
                            if (has(orig, g, nh))
                                ones++;
                        }
                    }
                }
                free(orig);
            }
        }
        gl = gr;
    }
    long long answer = 1337LL * all - 1335LL * within - ones;
    free(psum);
    free(pw);
    free(pref);
    free(bad);
    free(idx);
    free(sigs);
    free(strs);
    psum = pw = pref = NULL;
    bad = idx = NULL;
    sigs = strs = NULL;
    return answer;
}
// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     char tmp[200005];
//     scanf("%s", tmp);
//     int length = (int)strlen(tmp);
//     char *input = malloc((size_t)n * (length + 1));
//     memcpy(input, tmp, (size_t)length + 1);
//     for (int i = 1; i < n; i++)
//         scanf("%s", input + (size_t)i * (length + 1));
//     printf("%lld\n", solver(n, length, input));
//     free(input);
//     return 0;
// }
