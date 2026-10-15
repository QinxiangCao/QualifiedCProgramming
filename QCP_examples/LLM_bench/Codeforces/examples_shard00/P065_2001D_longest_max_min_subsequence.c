/* Codeforces 2001/D - Longest Max Min Subsequence */
// #include <stdio.h>
// #include <stdlib.h>
// #include <limits.h>
typedef struct
{
    int last, value;
} HeapNode;
typedef struct
{
    int maxv, maxp, minv, minp;
} Node;
static void hp_push(HeapNode *h, int *sz, HeapNode x)
{
    int i = ++*sz;
    while (i > 1 && h[i / 2].last > x.last)
    {
        h[i] = h[i / 2];
        i /= 2;
    }
    h[i] = x;
}
static HeapNode hp_pop(HeapNode *h, int *sz)
{
    HeapNode r = h[1], x = h[(*sz)--];
    int i = 1;
    while (i * 2 <= *sz)
    {
        int c = i * 2;
        if (c + 1 <= *sz && h[c + 1].last < h[c].last)
            ++c;
        if (h[c].last >= x.last)
            break;
        h[i] = h[c];
        i = c;
    }
    h[i] = x;
    return r;
}
static Node merge(Node a, Node b)
{
    Node r;
    if (a.maxv > b.maxv || (a.maxv == b.maxv && a.maxp < b.maxp))
    {
        r.maxv = a.maxv;
        r.maxp = a.maxp;
    }
    else
    {
        r.maxv = b.maxv;
        r.maxp = b.maxp;
    }
    if (a.minv < b.minv || (a.minv == b.minv && a.minp < b.minp))
    {
        r.minv = a.minv;
        r.minp = a.minp;
    }
    else
    {
        r.minv = b.minv;
        r.minp = b.minp;
    }
    return r;
}
/* QCP_INSERT_BEGIN:P065_2001D_longest_max_min_subsequence.support */
/*@ Extern Coq
      (Spec : list Z -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P065_2001D_longest_max_min_subsequence_lib */
/* QCP_INSERT_END:P065_2001D_longest_max_min_subsequence.support */
static int solver(const int *input, int n,
                  int *out) /* QCP_INSERT_BEGIN:P065_2001D_longest_max_min_subsequence.contract */

/*@ With (a : list Z)
    Require
      1 <= Zlength(a) && Zlength(a) <= 300000 &&
      (forall i, (0 <= i && i < Zlength(a)) => (1 <= a[i] && a[i] <= Zlength(a))) &&
      n == Zlength(a) &&
      IntArray::full(input, n, a) * IntArray::undef_full(out, n)
    Ensure
      exists result,
        Spec(a, result) && __return == Zlength(result) &&
        IntArray::full(input, n, a) *
        IntArray::full(out, Zlength(result), result) *
        IntArray::undef_seg(out, Zlength(result), n)
*/
/* QCP_INSERT_END:P065_2001D_longest_max_min_subsequence.contract */
{
    int *a = malloc((size_t)n * sizeof(*a)), *last = malloc(((size_t)n + 1) * sizeof(*last)),
        *head = malloc(((size_t)n + 1) * sizeof(*head)), *next = malloc((size_t)n * sizeof(*next));
    unsigned char *chosen = calloc((size_t)n + 1, 1);
    for (int i = 0; i <= n; ++i)
    {
        last[i] = -1;
        head[i] = -1;
    }
    for (int i = 0; i < n; ++i)
    {
        a[i] = input[i];
        last[a[i]] = i;
        next[i] = head[a[i]];
        head[a[i]] = i;
    }
    int distinct = 0;
    HeapNode *heap = malloc(((size_t)n + 1) * sizeof(*heap));
    int hs = 0;
    for (int v = 1; v <= n; ++v)
        if (last[v] >= 0)
        {
            ++distinct;
            hp_push(heap, &hs, (HeapNode){last[v], v});
        }
    int size = 1;
    while (size < n)
        size *= 2;
    Node *seg = malloc((size_t)(2 * size) * sizeof(*seg));
    Node empty = {-1, INT_MAX, INT_MAX, INT_MAX};
    for (int i = 0; i < 2 * size; ++i)
        seg[i] = empty;
    for (int i = 0; i < n; ++i)
        seg[size + i] = (Node){a[i], i, a[i], i};
    for (int i = size - 1; i; --i)
        seg[i] = merge(seg[2 * i], seg[2 * i + 1]);
    int left = 0;
    for (int step = 0; step < distinct; ++step)
    {
        while (hs && chosen[heap[1].value])
            hp_pop(heap, &hs);
        int right = heap[1].last, l = left + size, r = right + 1 + size;
        Node L = empty, R = empty;
        while (l < r)
        {
            if (l & 1)
                L = merge(L, seg[l++]);
            if (r & 1)
                R = merge(seg[--r], R);
            l /= 2;
            r /= 2;
        }
        Node got = merge(L, R);
        int pos = (step % 2 == 0) ? got.maxp : got.minp, val = a[pos];
        out[step] = val;
        left = pos + 1;
        chosen[val] = 1;
        for (int p = head[val]; p != -1; p = next[p])
        {
            int z = size + p;
            seg[z] = empty;
            for (z /= 2; z; z /= 2)
                seg[z] = merge(seg[2 * z], seg[2 * z + 1]);
        }
    }
    free(a);
    free(last);
    free(head);
    free(next);
    free(chosen);
    free(heap);
    free(seg);
    return distinct;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n;
//         scanf("%d", &n);
//         int *a = malloc((size_t)n * sizeof(*a)), *out = malloc((size_t)n * sizeof(*out));
//         for (int i = 0; i < n; ++i)
//             scanf("%d", &a[i]);
//         int distinct = solver(a, n, out);
//         printf("%d\n", distinct);
//         for (int i = 0; i < distinct; ++i)
//             printf("%d%c", out[i], i + 1 == distinct ? '\n' : ' ');
//         free(a);
//         free(out);
//     }
//     return 0;
// }
