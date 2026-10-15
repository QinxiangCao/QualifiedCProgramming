/* Codeforces 547/C - Mike and Foam */
// #include <stdio.h>
// #include <stdlib.h>
#define MAXA 500000
/* QCP_INSERT_BEGIN:P083_547C_mike_and_foam.support */
/*@ Extern Coq
      (Spec : list Z -> list Z -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P083_547C_mike_and_foam_lib */
/* QCP_INSERT_END:P083_547C_mike_and_foam.support */
static void solver(int n, const int *a, int q, const int *queries,
                   long long *out) /* QCP_INSERT_BEGIN:P083_547C_mike_and_foam.contract */

/*@ With (foam : list Z)
             (queries_data : list Z)
             (query_indices : list Z)
    Require
      1 <= Zlength(foam) && Zlength(foam) <= 200000 &&
      1 <= Zlength(queries_data) && Zlength(queries_data) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(foam)) => (1 <= foam[i] && foam[i] <= 500000)) &&
      (forall i, (0 <= i && i < Zlength(queries_data)) => (1 <= queries_data[i] && queries_data[i] <= Zlength(foam))) &&
      n == Zlength(foam) && q == Zlength(queries_data) &&
      Zlength(query_indices) == q &&
      (forall i, (0 <= i && i < q) => queries_data[i] == query_indices[i] + 1) &&
      IntArray::full(a, n, foam) *
      IntArray::full(queries, q, query_indices) *
      Int64Array::undef_full(out, q)
    Ensure
      exists result,
        Spec(foam, queries_data, result) &&
        IntArray::full(a, n, foam) *
        IntArray::full(queries, q, query_indices) *
        Int64Array::full(out, q, result)
*/
/* QCP_INSERT_END:P083_547C_mike_and_foam.contract */
{
    int *spf = calloc(MAXA + 1, sizeof(*spf));
    for (int i = 2; i <= MAXA; ++i)
        if (!spf[i])
        {
            spf[i] = i;
            if ((long long)i * i <= MAXA)
                for (int j = i * i; j <= MAXA; j += i)
                    if (!spf[j])
                        spf[j] = i;
        }
    int *cnt = calloc(MAXA + 1, sizeof(*cnt));
    unsigned char *active = calloc((size_t)n, 1);
    long long answer = 0;
    for (int z = 0; z < q; ++z)
    {
        int x = queries[z], value = a[x], primes[10], pc = 0;
        while (value > 1)
        {
            int p = spf[value];
            primes[pc++] = p;
            while (value % p == 0)
                value /= p;
        }
        int subsets = 1 << pc, divs[1024], sign[1024];
        for (int mask = 0; mask < subsets; ++mask)
        {
            int d = 1, bits = 0;
            for (int i = 0; i < pc; ++i)
                if (mask >> i & 1)
                {
                    d *= primes[i];
                    ++bits;
                }
            divs[mask] = d;
            sign[mask] = (bits & 1) ? -1 : 1;
        }
        if (!active[x])
        {
            long long cop = 0;
            for (int i = 0; i < subsets; ++i)
                cop += (long long)sign[i] * cnt[divs[i]];
            answer += cop;
            for (int i = 0; i < subsets; ++i)
                ++cnt[divs[i]];
            active[x] = 1;
        }
        else
        {
            for (int i = 0; i < subsets; ++i)
                --cnt[divs[i]];
            long long cop = 0;
            for (int i = 0; i < subsets; ++i)
                cop += (long long)sign[i] * cnt[divs[i]];
            answer -= cop;
            active[x] = 0;
        }
        out[z] = answer;
    }
    free(spf);
    free(cnt);
    free(active);
}
// int main(void)
// {
//     int n, q;
//     if (scanf("%d %d", &n, &q) != 2)
//         return 0;
//     int *a = malloc((size_t)n * sizeof(*a)), *queries = malloc((size_t)q * sizeof(*queries));
//     long long *out = malloc((size_t)q * sizeof(*out));
//     for (int i = 0; i < n; ++i)
//         scanf("%d", &a[i]);
//     for (int i = 0; i < q; ++i)
//     {
//         scanf("%d", &queries[i]);
//         --queries[i];
//     }
//     solver(n, a, q, queries, out);
//     for (int i = 0; i < q; ++i)
//         printf("%lld\n", out[i]);
//     free(a);
//     free(queries);
//     free(out);
//     return 0;
// }
