/*
 * Codeforces 896/E - Welcome home, Chtholly  (rating 3100, OPSEQ)
 *
 * Op 1 (l,r,x): for i in [l,r], if a_i > x then a_i -= x.
 * Op 2 (l,r,x): count i in [l,r] with a_i == x.
 *
 * sqrt decomposition. Each block keeps its values in value-buckets via a union-
 * find plus a lazy `tag` (real value = bucket - tag). A full-block op 1 with
 * threshold x either shifts everything down (tag += x) and merges the kept low
 * part [1,x] into [x+1,2x] when 2x <= max, or merges the high part [x+1,max]
 * down into [1,max-x] when 2x > max -- always touching only the smaller side,
 * which is O(min(x, max-x)) and amortizes to O((n+m) sqrt(n)). A full-block
 * op 2 is one bucket lookup. Partial blocks are rebuilt from the real values.
 * Buckets are reset lazily by a per-block version stamp.
 *
 * solver() takes the raw array and the raw operation list, builds the whole
 * decomposition itself and returns every op-2 answer; main() only reads the
 * input and prints those answers.
 */

// #include <stdio.h>
// #include <stdlib.h>

#define MAXV 100000

static int n, m, B, nb;
static int *par, *cnt, *ver;   /* flat [block * stride + label] */
static int stride;             /* MAXV + 2 */
static int *bver, *tag, *bmax; /* per-block version / tag / max real value */
static int *pb;                /* position -> bucket label */

static inline int IDX(int bk, int v)
{
    return bk * stride + v;
}
static inline int getpar(int bk, int v)
{
    int i = IDX(bk, v);
    return ver[i] == bver[bk] ? par[i] : 0;
}
static inline int getcnt(int bk, int v)
{
    int i = IDX(bk, v);
    return ver[i] == bver[bk] ? cnt[i] : 0;
}
static inline void setpar(int bk, int v, int p)
{
    int i = IDX(bk, v);
    par[i] = p;
    cnt[i] = (ver[i] == bver[bk]) ? cnt[i] : 0;
    ver[i] = bver[bk];
}
static inline void setcnt(int bk, int v, int c)
{
    int i = IDX(bk, v);
    cnt[i] = c;
    par[i] = (ver[i] == bver[bk]) ? par[i] : 0;
    ver[i] = bver[bk];
}

static int find(int bk, int v)
{
    int r = v, p;
    while ((p = getpar(bk, r)) != 0)
        r = p;
    while (v != r)
    {
        p = getpar(bk, v);
        setpar(bk, v, r);
        v = p;
    }
    return r;
}

static void build_block(int bk)
{
    bver[bk]++; /* invalidate all old buckets */
    tag[bk] = 0;
    int lo = bk * B + 1, hi = lo + B - 1;
    if (hi > n)
        hi = n;
    int mx = 0;
    for (int i = lo; i <= hi; i++)
    {
        int v = pb[i]; /* pb holds the (real) value during rebuild */
        setcnt(bk, v, getcnt(bk, v) + 1);
        if (v > mx)
            mx = v;
    }
    bmax[bk] = mx;
}

/* full-block op 1 */
static void block_op1(int bk, int x)
{
    int M = bmax[bk], t = tag[bk];
    if (x >= M)
        return;
    if (2 * x <= M)
    { /* merge kept [1,x] into [x+1,2x] */
        for (int v = 1; v <= x; v++)
        {
            int a = find(bk, v + t), b = find(bk, v + x + t);
            if (a != b)
            {
                setpar(bk, a, b);
                setcnt(bk, b, getcnt(bk, b) + getcnt(bk, a));
                setcnt(bk, a, 0);
            }
        }
        tag[bk] = t + x;
        bmax[bk] = M - x;
    }
    else
    { /* merge high [x+1,M] down by x */
        for (int v = x + 1; v <= M; v++)
        {
            int a = find(bk, v + t), b = find(bk, v - x + t);
            if (a != b)
            {
                setpar(bk, a, b);
                setcnt(bk, b, getcnt(bk, b) + getcnt(bk, a));
                setcnt(bk, a, 0);
            }
        }
        int nm = x;
        while (nm >= 1 && getcnt(bk, nm + t) == 0)
            nm--; /* true new max */
        bmax[bk] = nm;
    }
}

/* rebuild a block into pb[] (real values), optionally applying op1 to [ql,qr] */
static void rebuild_apply(int bk, int ql, int qr, int x, int isop1)
{
    int lo = bk * B + 1, hi = lo + B - 1;
    if (hi > n)
        hi = n;
    int t = tag[bk];
    for (int i = lo; i <= hi; i++)
    {
        int cur = find(bk, pb[i]) - t; /* real value */
        if (isop1 && i >= ql && i <= qr && cur > x)
            cur -= x;
        pb[i] = cur; /* store real value temporarily */
    }
    build_block(bk); /* re-bucket from pb[] */
}

static void apply_op1(int l, int r, int x)
{
    int bl = (l - 1) / B, br = (r - 1) / B;
    if (bl == br)
    {
        rebuild_apply(bl, l, r, x, 1);
        return;
    }
    rebuild_apply(bl, l, (bl + 1) * B, x, 1);
    rebuild_apply(br, br * B + 1, r, x, 1);
    for (int bk = bl + 1; bk < br; bk++)
        block_op1(bk, x);
}

static long long apply_op2(int l, int r, int x)
{
    int bl = (l - 1) / B, br = (r - 1) / B;
    long long ans = 0;
    if (bl == br)
    {
        int t = tag[bl];
        for (int i = l; i <= r; i++)
            if (find(bl, pb[i]) - t == x)
                ans++;
        return ans;
    }
    int t = tag[bl];
    for (int i = l; i <= (bl + 1) * B; i++)
        if (find(bl, pb[i]) - t == x)
            ans++;
    t = tag[br];
    for (int i = br * B + 1; i <= r; i++)
        if (find(br, pb[i]) - t == x)
            ans++;
    for (int bk = bl + 1; bk < br; bk++)
        if (x <= bmax[bk])
            ans += getcnt(bk, x + tag[bk]);
    return ans;
}

/* solver: pure. a[0..nn-1] is the raw array; the mm operations are the raw
 * quadruples (op[i], ql[i], qr[i], qx[i]). Builds the sqrt decomposition itself,
 * writes one answer per op-2 into out and returns the number of answers. */
/* QCP_INSERT_BEGIN:P100_896E_welcome_home_chtholly.support */
/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
      (zquad_1 : Z * Z * Z * Z -> Z)
      (zquad_2 : Z * Z * Z * Z -> Z)
      (zquad_3 : Z * Z * Z * Z -> Z)
      (zquad_4 : Z * Z * Z * Z -> Z)
      (Spec : list Z -> list (Z * Z * Z * Z) -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P100_896E_welcome_home_chtholly_lib */
/* QCP_INSERT_END:P100_896E_welcome_home_chtholly.support */
static int solver(int nn, int mm, const int *a, const int *op, const int *ql, const int *qr,
                  const int *qx,
                  long long *out) /* QCP_INSERT_BEGIN:P100_896E_welcome_home_chtholly.contract */

/*@ With (input : list Z)
             (operations : list (Z * Z * Z * Z))
             (kinds lefts rights values : list Z)
    Require
      1 <= nn && nn <= 100000 &&
      1 <= mm && mm <= 100000 &&
      nn == Zlength(input) && mm == Zlength(operations) &&
      Zlength(kinds) == mm && Zlength(lefts) == mm &&
      Zlength(rights) == mm && Zlength(values) == mm &&
      (forall i, (0 <= i && i < nn) =>
        (1 <= input[i] && input[i] <= 100000)) &&
      (forall i, (0 <= i && i < mm) =>
        ((zquad_1(operations[i]) == 1 || zquad_1(operations[i]) == 2) &&
         0 <= zquad_2(operations[i]) &&
         zquad_2(operations[i]) <= zquad_3(operations[i]) &&
         zquad_3(operations[i]) < nn &&
         1 <= zquad_4(operations[i]) && zquad_4(operations[i]) <= 100000 &&
         zquad_1(operations[i]) == kinds[i] &&
         zquad_2(operations[i]) == lefts[i] - 1 &&
         zquad_3(operations[i]) == rights[i] - 1 &&
         zquad_4(operations[i]) == values[i])) &&
      IntArray::full(a, nn, input) *
      IntArray::full(op, mm, kinds) *
      IntArray::full(ql, mm, lefts) *
      IntArray::full(qr, mm, rights) *
      IntArray::full(qx, mm, values) *
      Int64Array::undef_full(out, mm)
    Ensure
      exists answers,
        Spec(input, operations, answers) && __return == Zlength(answers) &&
        IntArray::full(a, nn, input) * IntArray::full(op, mm, kinds) *
        IntArray::full(ql, mm, lefts) * IntArray::full(qr, mm, rights) *
        IntArray::full(qx, mm, values) *
        Int64Array::full(out, __return, answers) * Int64Array::undef_seg(out, __return, mm)
*/
/* QCP_INSERT_END:P100_896E_welcome_home_chtholly.contract */

{
    n = nn;
    m = mm;
    pb = malloc((n + 1) * sizeof(int));
    for (int i = 1; i <= n; i++)
        pb[i] = a[i - 1];

    B = 700;
    nb = (n + B - 1) / B;
    stride = MAXV + 2;
    par = calloc((size_t)nb * stride, sizeof(int));
    cnt = calloc((size_t)nb * stride, sizeof(int));
    ver = calloc((size_t)nb * stride, sizeof(int));
    bver = calloc(nb, sizeof(int));
    tag = calloc(nb, sizeof(int));
    bmax = calloc(nb, sizeof(int));
    for (int bk = 0; bk < nb; bk++)
        build_block(bk);

    int nout = 0;
    for (int i = 0; i < m; i++)
    {
        if (op[i] == 1)
            apply_op1(ql[i], qr[i], qx[i]);
        else
            out[nout++] = apply_op2(ql[i], qr[i], qx[i]);
    }

    free(pb);
    free(par);
    free(cnt);
    free(ver);
    free(bver);
    free(tag);
    free(bmax);
    pb = par = cnt = ver = bver = tag = bmax = NULL;
    return nout;
}

// int main(void)
// {
//     int nn, mm;
//     if (scanf("%d %d", &nn, &mm) != 2)
//         return 0;
//     int *a = malloc(nn * sizeof(int));
//     for (int i = 0; i < nn; i++) scanf("%d", &a[i]);

//     int *op = malloc((mm ? mm : 1) * sizeof(int));
//     int *ql = malloc((mm ? mm : 1) * sizeof(int));
//     int *qr = malloc((mm ? mm : 1) * sizeof(int));
//     int *qx = malloc((mm ? mm : 1) * sizeof(int));
//     for (int i = 0; i < mm; i++)
//         scanf("%d %d %d %d", &op[i], &ql[i], &qr[i], &qx[i]);

//     long long *out = malloc((mm ? mm : 1) * sizeof(long long));
//     int nout = solver(nn, mm, a, op, ql, qr, qx, out);
//     for (int i = 0; i < nout; i++)
//         printf("%lld\n", out[i]);

//     free(a); free(op); free(ql); free(qr); free(qx); free(out);
//     return 0;
// }
