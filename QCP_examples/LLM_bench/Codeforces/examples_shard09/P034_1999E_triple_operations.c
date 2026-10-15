/*
 * Codeforces 1999/E - Triple Operations  (rating 1300, MATH)
 *
 * Write f(x) for the number of base-3 digits of x, i.e. how many divisions by
 * 3 drive x to 0.  Every operation performs one division on some y (and one
 * multiplication, which is free if x is already 0).  Zeroing the smallest
 * number l first costs f(l), and pairing it with each remaining number costs
 * f(i) each, so the total is 2*f(l) + sum_{i=l+1..r} f(i).
 *
 * The tables are shared by every query, so solver() takes the whole query set
 * and builds them itself; main() only reads and prints.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : Z -> Z -> Prop)
      (Spec : Z -> Z -> Z -> Prop)
      (TripleTablesBridge : list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (TripleTablesPrefix : list Z -> list Z -> Z -> Prop)
      (TripleOutputsPrefix : list Z -> list Z -> list Z -> Z -> Prop)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Extern Coq
      (TripleClosedFormBridge : list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P034_1999E_triple_operations_lib */

#define MAXN 200005
#define MAXQ 10005

static long long pre[MAXN];               /* pre[i] = sum of f(1..i) */
static int fv[MAXN];                      /* fv[i]  = f(i) */

/* solver: reads no input.  Answers query i as out[i], for l[i] < r[i].  Builds
 * the file-scope tables `fv` and `pre` on every call, so it is not free of
 * global-state writes. */
static void solver(int q, const int *l, const int *r, long long *out)
/* QCP_INSERT_BEGIN:shard09-P034-solver-contract */
/*@ With (ls : list Z) (rs : list Z)
    Require
      1 <= q && q <= 10000 &&
      Zlength(ls) == q && Zlength(rs) == q &&
      (forall i, (0 <= i && i < q) => (1 <= ls[i] && ls[i] < rs[i] && rs[i] <= 200000)) &&
      IntArray::full(l, q, ls) * IntArray::full(r, q, rs) *
      Int64Array::undef_full(out, q) *
      IntArray::undef_full(fv, 200005) * Int64Array::undef_full(pre, 200005)
    Ensure
      exists (outs : list Z) (fvs : list Z) (pres : list Z),
        Zlength(outs) == q &&
        (forall i, (0 <= i && i < q) => Spec(ls[i], rs[i], outs[i])) &&
        TripleTablesBridge(fvs, pres) &&
        IntArray::full(l, q, ls) * IntArray::full(r, q, rs) *
        Int64Array::full(out, q, outs) *
        IntArray::full(fv, 200005, fvs) * Int64Array::full(pre, 200005, pres)
*/
/* QCP_INSERT_END:shard09-P034-solver-contract */
{
    fv[0] = 0;
    pre[0] = 0;
    /*@ Inv Assert
          exists (fvs : list Z) (pres : list Z),
            q == q@pre && l == l@pre && r == r@pre && out == out@pre &&
            1 <= q@pre && q@pre <= 10000 &&
            Zlength(ls) == q@pre && Zlength(rs) == q@pre &&
            (forall k, (0 <= k && k < q@pre) =>
              (1 <= ls[k] && ls[k] < rs[k] && rs[k] <= 200000)) &&
            1 <= i && i <= 200005 &&
            TripleTablesPrefix(fvs, pres, i) &&
            IntArray::full(l, q@pre, ls) * IntArray::full(r, q@pre, rs) *
            Int64Array::undef_full(out, q@pre) *
            IntArray::seg(fv, 0, i, fvs) * IntArray::undef_seg(fv, i, 200005) *
            Int64Array::seg(pre, 0, i, pres) * Int64Array::undef_seg(pre, i, 200005)
    */
    for (int i = 1; i < MAXN; i++) {
        /*@ 0 <= i / 3 && i / 3 < i by local */
        fv[i] = fv[i / 3] + 1;
        pre[i] = pre[i - 1] + fv[i];
    }
    /*@ Inv Assert
          exists (fvs : list Z) (pres : list Z) (outs : list Z),
            q == q@pre && l == l@pre && r == r@pre && out == out@pre &&
            1 <= q@pre && q@pre <= 10000 &&
            Zlength(ls) == q@pre && Zlength(rs) == q@pre &&
            (forall k, (0 <= k && k < q@pre) =>
              (1 <= ls[k] && ls[k] < rs[k] && rs[k] <= 200000)) &&
            0 <= i && i <= q@pre &&
            TripleTablesPrefix(fvs, pres, 200005) &&
            TripleTablesBridge(fvs, pres) &&
            TripleClosedFormBridge(fvs, pres) &&
            TripleOutputsPrefix(ls, rs, outs, i) &&
            IntArray::full(l, q@pre, ls) * IntArray::full(r, q@pre, rs) *
            Int64Array::seg(out, 0, i, outs) * Int64Array::undef_seg(out, i, q@pre) *
            IntArray::full(fv, 200005, fvs) * Int64Array::full(pre, 200005, pres)
    */
    for (int i = 0; i < q; i++)
        out[i] = 2LL * fv[l[i]] + (pre[r[i]] - pre[l[i]]);
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int l[MAXQ], r[MAXQ];
//     static long long out[MAXQ];
//     for (int i = 0; i < t; i++)
//         scanf("%d %d", &l[i], &r[i]);
//     solver(t, l, r, out);
//     for (int i = 0; i < t; i++)
//         printf("%lld\n", out[i]);
//     return 0;
// }
