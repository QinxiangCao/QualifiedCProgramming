// #include <stdio.h>
// #include <stdlib.h>
// #include <stdint.h>
typedef struct
{
    int x, y;
} State;
typedef uint64_t u64;
static u64 *syn;
static int q;
static int synergy(int x, int y)
{
    u64 k = ((u64)(unsigned)x << 32) | (unsigned)y;
    int l = 0, r = q;
    while (l < r)
    {
        int m = (l + r) / 2;
        if (syn[m] < k)
            l = m + 1;
        else
            r = m;
    }
    return l < q && syn[l] == k;
}
static int cmp64(const void *A, const void *B)
{
    u64 a = *(const u64 *)A, b = *(const u64 *)B;
    return a < b ? -1 : a > b;
}
static int cmps(const void *A, const void *B)
{
    const State *a = A, *b = B;
    return a->x == b->x ? b->y - a->y : a->x - b->x;
}
/* QCP_INSERT_BEGIN:P097_1612F_armor_and_weapons.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : Z -> Z -> list (Z * Z) -> Prop)
      (Spec : Z -> Z -> list (Z * Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P097_1612F_armor_and_weapons_lib */
/* QCP_INSERT_END:P097_1612F_armor_and_weapons.support */
static int solver(int n, int m, int synergy_count, const int *sx,
                  const int *sy) /* QCP_INSERT_BEGIN:P097_1612F_armor_and_weapons.contract */

/*@ With (synergies : list (Z * Z))
             (sx_data sy_data : list Z)
    Require
      2 <= n && n <= 200000 &&
      2 <= m && m <= 200000 &&
      Zlength(synergies) <= 200000 &&
      Pre(n, m, synergies) &&
      synergy_count == Zlength(synergies) &&
      Zlength(sx_data) == Zlength(synergies) && Zlength(sy_data) == Zlength(synergies) &&
      (forall i, (0 <= i && i < Zlength(synergies)) =>
        (sx_data[i] == fst(synergies[i]) && sy_data[i] == snd(synergies[i]))) &&
      IntArray::full(sx, synergy_count, sx_data) *
      IntArray::full(sy, synergy_count, sy_data)
    Ensure
      Spec(n, m, synergies, __return) &&
      IntArray::full(sx, synergy_count, sx_data) *
      IntArray::full(sy, synergy_count, sy_data)
*/
/* QCP_INSERT_END:P097_1612F_armor_and_weapons.contract */
{
    q = synergy_count;
    syn = malloc((size_t)q * sizeof *syn);
    for (int i = 0; i < q; i++)
        syn[i] = ((u64)(unsigned)sx[i] << 32) | (unsigned)sy[i];
    qsort(syn, q, sizeof *syn, cmp64);
    int cap = 4 * (n < m ? n : m) + 100;
    State *cur = malloc((size_t)cap * sizeof *cur), *nxt = malloc((size_t)2 * cap * sizeof *nxt);
    int cs = 1, dist = 0;
    cur[0] = (State){1, 1};
    while (1)
    {
        for (int i = 0; i < cs; i++)
            if (cur[i].x == n && cur[i].y == m)
            {
                free(nxt);
                free(cur);
                free(syn);
                syn = NULL;
                return dist;
            }
        int ns = 0;
        for (int i = 0; i < cs; i++)
        {
            int p = cur[i].x + cur[i].y + synergy(cur[i].x, cur[i].y), x = p < n ? p : n,
                y = p < m ? p : m;
            if (x != cur[i].x)
                nxt[ns++] = (State){x, cur[i].y};
            if (y != cur[i].y)
                nxt[ns++] = (State){cur[i].x, y};
        }
        qsort(nxt, ns, sizeof *nxt, cmps);
        int keep = 0, maxy = -1;
        for (int i = ns - 1; i >= 0;)
        {
            int x = nxt[i].x, j = i, besty = nxt[i].y;
            while (j >= 0 && nxt[j].x == x)
            {
                if (nxt[j].y > besty)
                    besty = nxt[j].y;
                j--;
            }
            if (besty > maxy)
            {
                cur[keep++] = (State){x, besty};
                maxy = besty;
            }
            i = j;
        }
        cs = keep;
        dist++;
    }
}
// int main(void)
// {
//     int n, m, synergy_count;
//     if (scanf("%d%d%d", &n, &m, &synergy_count) != 3)
//         return 0;
//     int *sx = malloc((size_t)synergy_count * sizeof *sx),
//         *sy = malloc((size_t)synergy_count * sizeof *sy);
//     for (int i = 0; i < synergy_count; i++)
//         scanf("%d%d", &sx[i], &sy[i]);
//     printf("%d\n", solver(n, m, synergy_count, sx, sy));
//     free(sx);
//     free(sy);
//     return 0;
// }
