/*
 * Codeforces 498/D - Traffic Jams in the Land  (rating 2400, SEGMENT TREE)
 *
 * Every period divides 60 = lcm(2..6), so a segment's behaviour is fully
 * described by the 60 travel times, one per arrival time modulo 60.  Each node
 * stores that table; merging is f(r) = fl(r) + fr((r + fl(r)) mod 60), and a
 * point update rebuilds one leaf and its ancestors.
 *
 * The input is a single instance holding q queries, so solver() builds the tree
 * and answers all of them; main() only reads and prints.
 */

// #include <stdio.h>
#include "array2_ext_def.h"
/* QCP_INSERT_BEGIN:shard09-P085-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P085_498D_traffic_jams_in_the_land_lib */
/*@ Extern Coq
      (pair : {A} {B} -> A -> B -> A * B)
      (Spec : list Z -> list (Z * Z * Z) -> list Z -> Prop)
*/

/* QCP_INSERT_END:shard09-P085-solver-support */

/*@ Extern Coq
      (cross : list Z -> Z -> Z)
      (delta : list Z -> Z -> Z)
      (PeriodsOK : list Z -> Prop)
      (NodeSlice : list Z -> Z -> Z -> list Z)
      (QuerySlice : list Z -> Z -> Z -> Z -> Z -> list Z)
      (NodeFits : Z -> Z -> Z -> Prop)
      (RowIs : list (list (option Z)) -> Z -> list Z -> Prop)
      (RowPrefixIs : list (list (option Z)) -> Z -> list Z -> Z -> Prop)
      (TreeOK : list (list (option Z)) -> list Z -> Z -> Z -> Z -> Prop)
      (RowsAgreeExcept :
         Z -> list (list (option Z)) -> list (list (option Z)) -> Prop)
      (CellsAgreeOutside :
         Z -> Z -> Z -> list (list (option Z)) -> list (list (option Z)) -> Prop)
      (CellsShaped : list (list (option Z)) -> Prop)
      (AgreeExceptIdx : Z -> list Z -> list Z -> Prop)
      (TreeStaleAt :
         list (list (option Z)) -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (AskCount : list (Z * Z * Z) -> Z -> Z)
      (QueryStepsOK : list (Z * Z * Z) -> list (list Z) -> Z -> Prop)
      (AnswersOK :
         list (Z * Z * Z) -> list (list Z) -> list Z -> Z -> Prop)
*/

#define MAXN 100005
#define MAXQ 100005
#define P 60

/* file-scope work arrays, rebuilt on every call */
static int seg[4 * MAXN][P];
static int a_[MAXN];                      /* current periods */

/* pull: combine the two children of node v. */
static void pull(int v)
/*@ With (cells : list (list (option Z))) (arr : list Z)
         (lo : Z) (mid : Z) (hi : Z)
    Require
      1 <= v && 2 * v + 1 < 400020 &&
      1 <= lo && lo <= mid && mid < hi && hi <= Zlength(arr) &&
      Zlength(arr) <= 100000 &&
      PeriodsOK(arr) && CellsShaped(cells) &&
      RowIs(cells, 2 * v, NodeSlice(arr, lo, mid)) &&
      RowIs(cells, 2 * v + 1, NodeSlice(arr, mid + 1, hi)) &&
      IntArray2::mixed_full(seg, 400020, 60, cells)
    Ensure
      exists (cells1 : list (list (option Z))),
        CellsShaped(cells1) &&
        RowIs(cells1, v@pre, NodeSlice(arr, lo, hi)) &&
        RowsAgreeExcept(v@pre, cells, cells1) &&
        IntArray2::mixed_full(seg, 400020, 60, cells1)
*/
{
    /*@ Inv Assert
        exists (cellsr : list (list (option Z))),
          v == v@pre &&
          1 <= v@pre && 2 * v@pre + 1 < 400020 &&
          1 <= lo && lo <= mid && mid < hi && hi <= Zlength(arr) &&
          Zlength(arr) <= 100000 &&
          0 <= r && r <= 60 &&
          PeriodsOK(arr) && CellsShaped(cellsr) &&
          RowIs(cellsr, 2 * v@pre, NodeSlice(arr, lo, mid)) &&
          RowIs(cellsr, 2 * v@pre + 1, NodeSlice(arr, mid + 1, hi)) &&
          RowPrefixIs(cellsr, v@pre, NodeSlice(arr, lo, hi), r) &&
          RowsAgreeExcept(v@pre, cells, cellsr) &&
          IntArray2::mixed_full(seg, 400020, 60, cellsr)
    */
    for (int r = 0; r < P; r++) {
        int left = seg[2 * v][r];
        /*@ Assert
            exists (cellsr : list (list (option Z))),
              v == v@pre &&
              1 <= v@pre && 2 * v@pre + 1 < 400020 &&
              1 <= lo && lo <= mid && mid < hi && hi <= Zlength(arr) &&
              Zlength(arr) <= 100000 &&
              0 <= r && r < 60 &&
              left == delta(NodeSlice(arr, lo, mid), r) &&
              1 <= left && left <= 2 * (mid - lo + 1) &&
              0 <= (r + left) % P && (r + left) % P < P &&
              PeriodsOK(arr) && CellsShaped(cellsr) &&
              RowIs(cellsr, 2 * v@pre, NodeSlice(arr, lo, mid)) &&
              RowIs(cellsr, 2 * v@pre + 1, NodeSlice(arr, mid + 1, hi)) &&
              RowPrefixIs(cellsr, v@pre, NodeSlice(arr, lo, hi), r) &&
              RowsAgreeExcept(v@pre, cells, cellsr) &&
              IntArray2::mixed_full(seg, 400020, 60, cellsr)
        */
        seg[v][r] = left + seg[2 * v + 1][(r + left) % P];
    }
}

static void build(int v, int lo, int hi)
/*@ With (cells : list (list (option Z))) (arr : list Z) (n : Z)
    Require
      NodeFits(v, lo, hi) && hi <= n &&
      n == Zlength(arr) && 1 <= n && n <= 100000 &&
      PeriodsOK(arr) && CellsShaped(cells) &&
      IntArray::seg(a_, 1, n + 1, arr) *
      IntArray2::mixed_full(seg, 400020, 60, cells)
    Ensure
      exists (cells1 : list (list (option Z))),
        CellsShaped(cells1) &&
        TreeOK(cells1, arr, v@pre, lo@pre, hi@pre) &&
        CellsAgreeOutside(v@pre, lo@pre, hi@pre, cells, cells1) &&
        IntArray::seg(a_, 1, n + 1, arr) *
        IntArray2::mixed_full(seg, 400020, 60, cells1)
*/
{
    if (lo == hi) {
        /*@ Inv Assert
            exists (cellsr : list (list (option Z))),
              v == v@pre && lo == lo@pre && hi == hi@pre && lo == hi &&
              NodeFits(v@pre, lo@pre, hi@pre) && 1 <= v@pre && v@pre < 400020 &&
              1 <= lo && lo <= n && hi <= n && n == Zlength(arr) && 1 <= n && n <= 100000 &&
              2 <= Znth(lo - 1, arr, 0) && Znth(lo - 1, arr, 0) <= 6 &&
              0 <= r && r <= 60 &&
              PeriodsOK(arr) && CellsShaped(cellsr) &&
              RowPrefixIs(cellsr, v@pre, NodeSlice(arr, lo, hi), r) &&
              RowsAgreeExcept(v@pre, cells, cellsr) &&
              IntArray::seg(a_, 1, n + 1, arr) *
              IntArray2::mixed_full(seg, 400020, 60, cellsr)
        */
        for (int r = 0; r < P; r++)
            seg[v][r] = (r % a_[lo] == 0) ? 2 : 1;
        return;
    }
    int mid = (lo + hi) / 2;
    build(2 * v, lo, mid) /*@ where arr = arr, n = n */;
    build(2 * v + 1, mid + 1, hi) /*@ where arr = arr, n = n */;
    /*@ Assert
        exists (cells2 : list (list (option Z))),
          v == v@pre && lo == lo@pre && hi == hi@pre &&
          NodeFits(v@pre, lo@pre, hi@pre) &&
          1 <= lo && lo <= mid && mid < hi && hi <= n &&
          n == Zlength(arr) && 1 <= n && n <= 100000 &&
          mid == (lo + hi) / 2 &&
          2 * v@pre + 1 < 400020 &&
          PeriodsOK(arr) && CellsShaped(cells2) &&
          TreeOK(cells2, arr, 2 * v@pre, lo, mid) &&
          TreeOK(cells2, arr, 2 * v@pre + 1, mid + 1, hi) &&
          CellsAgreeOutside(v@pre, lo@pre, hi@pre, cells, cells2) &&
          IntArray::seg(a_, 1, n + 1, arr) *
          IntArray2::mixed_full(seg, 400020, 60, cells2)
    */
    pull(v) /*@ where arr = arr, lo = lo, mid = mid, hi = hi */;
}

static void update(int v, int lo, int hi, int pos)
/*@ With (cells : list (list (option Z))) (arr : list Z) (n : Z)
    Require
      NodeFits(v, lo, hi) && hi <= n &&
      n == Zlength(arr) && 1 <= n && n <= 100000 &&
      lo <= pos && pos <= hi &&
      PeriodsOK(arr) && CellsShaped(cells) &&
      TreeStaleAt(cells, arr, v, lo, hi, pos) &&
      IntArray::seg(a_, 1, n + 1, arr) *
      IntArray2::mixed_full(seg, 400020, 60, cells)
    Ensure
      exists (cells1 : list (list (option Z))),
        CellsShaped(cells1) &&
        TreeOK(cells1, arr, v@pre, lo@pre, hi@pre) &&
        CellsAgreeOutside(v@pre, lo@pre, hi@pre, cells, cells1) &&
        IntArray::seg(a_, 1, n + 1, arr) *
        IntArray2::mixed_full(seg, 400020, 60, cells1)
*/
{
    if (lo == hi) {
        /*@ Inv Assert
            exists (cellsr : list (list (option Z))),
              v == v@pre && lo == lo@pre && hi == hi@pre && pos == pos@pre &&
              lo == hi && lo == pos &&
              NodeFits(v@pre, lo@pre, hi@pre) && 1 <= v@pre && v@pre < 400020 &&
              1 <= lo && lo <= n && hi <= n && n == Zlength(arr) && 1 <= n && n <= 100000 &&
              2 <= Znth(lo - 1, arr, 0) && Znth(lo - 1, arr, 0) <= 6 &&
              0 <= r && r <= 60 &&
              PeriodsOK(arr) && CellsShaped(cellsr) &&
              RowPrefixIs(cellsr, v@pre, NodeSlice(arr, lo, hi), r) &&
              RowsAgreeExcept(v@pre, cells, cellsr) &&
              IntArray::seg(a_, 1, n + 1, arr) *
              IntArray2::mixed_full(seg, 400020, 60, cellsr)
        */
        for (int r = 0; r < P; r++)
            seg[v][r] = (r % a_[lo] == 0) ? 2 : 1;
        return;
    }
    int mid = (lo + hi) / 2;
    if (pos <= mid)
        update(2 * v, lo, mid, pos) /*@ where arr = arr, n = n */;
    else
        update(2 * v + 1, mid + 1, hi, pos)
          /*@ where arr = arr, n = n */;
    /*@ Assert
        exists (cells2 : list (list (option Z))),
          v == v@pre && lo == lo@pre && hi == hi@pre && pos == pos@pre &&
          NodeFits(v@pre, lo@pre, hi@pre) &&
          1 <= lo && lo <= mid && mid < hi && hi <= n &&
          n == Zlength(arr) && 1 <= n && n <= 100000 &&
          mid == (lo + hi) / 2 && lo <= pos && pos <= hi &&
          2 * v@pre + 1 < 400020 &&
          PeriodsOK(arr) && CellsShaped(cells2) &&
          TreeOK(cells2, arr, 2 * v@pre, lo, mid) &&
          TreeOK(cells2, arr, 2 * v@pre + 1, mid + 1, hi) &&
          CellsAgreeOutside(v@pre, lo@pre, hi@pre, cells, cells2) &&
          IntArray::seg(a_, 1, n + 1, arr) *
          IntArray2::mixed_full(seg, 400020, 60, cells2)
    */
    pull(v) /*@ where arr = arr, lo = lo, mid = mid, hi = hi */;
}

/* query: time after crossing segments [ql, qr] starting at time t. */
static int query(int v, int lo, int hi, int ql, int qr, int t)
/*@ With (cells : list (list (option Z))) (arr : list Z) (n : Z)
    Require
      NodeFits(v, lo, hi) && hi <= n &&
      n == Zlength(arr) && 1 <= n && n <= 100000 &&
      1 <= ql && ql <= qr && qr <= n && lo <= qr && ql <= hi &&
      0 <= t && t + 2 * (hi - lo + 1) <= 400000 &&
      PeriodsOK(arr) && CellsShaped(cells) &&
      TreeOK(cells, arr, v, lo, hi) &&
      IntArray::seg(a_, 1, n + 1, arr) *
      IntArray2::mixed_full(seg, 400020, 60, cells)
    Ensure
      __return == cross(QuerySlice(arr, lo@pre, hi@pre, ql@pre, qr@pre), t@pre) &&
      t@pre <= __return && __return <= t@pre + 2 * (hi@pre - lo@pre + 1) &&
      IntArray::seg(a_, 1, n + 1, arr) *
      IntArray2::mixed_full(seg, 400020, 60, cells)
*/
{
    /*@ Assert
          v == v@pre && lo == lo@pre && hi == hi@pre &&
          ql == ql@pre && qr == qr@pre && t == t@pre &&
          NodeFits(v@pre, lo@pre, hi@pre) &&
          1 <= v@pre && v@pre < 400020 &&
          1 <= lo@pre && lo@pre <= hi@pre &&
          hi@pre <= n && n == Zlength(arr) && 1 <= n && n <= 100000 &&
          1 <= ql@pre && ql@pre <= qr@pre && qr@pre <= n &&
          lo@pre <= qr@pre && ql@pre <= hi@pre &&
          0 <= t@pre && t@pre + 2 * (hi@pre - lo@pre + 1) <= 400000 &&
          0 <= t@pre % P && t@pre % P < P &&
          PeriodsOK(arr) && CellsShaped(cells) &&
          TreeOK(cells, arr, v@pre, lo@pre, hi@pre) &&
          IntArray::seg(a_, 1, n + 1, arr) *
          IntArray2::mixed_full(seg, 400020, 60, cells)
    */
    if (ql <= lo && hi <= qr)
        return t + seg[v][t % P];
    int mid = (lo + hi) / 2;
    if (qr <= mid)
        return query(2 * v, lo, mid, ql, qr, t) /*@ where arr = arr, n = n */;
    if (ql > mid)
        return query(2 * v + 1, mid + 1, hi, ql, qr, t)
                 /*@ where arr = arr, n = n */;
    int mt = query(2 * v, lo, mid, ql, qr, t) /*@ where arr = arr, n = n */;
    return query(2 * v + 1, mid + 1, hi, ql, qr, mt)
             /*@ where arr = arr, n = n */;
}

/* solver: reads no input.  Runs the q queries against the periods a[1..n]:
 * type[i] == 'C' sets a[x] to y, otherwise the travel time from city x to city
 * y is appended to out[].  Returns how many answers were written, and writes
 * the file-scope work arrays above. */
static int solver(int n, const int *a, int q, const char *type,
                  const int *qx, const int *qy, int *out)
/* QCP_INSERT_BEGIN:shard09-P085-solver-contract */
/*@ With (periods : list Z) (kinds : list Z) (xs : list Z) (ys : list Z)
         (queries : list (Z * Z * Z))
    Require
      1 <= n && n <= 100000 && n == Zlength(periods) &&
      1 <= q && q <= 100000 && q == Zlength(kinds) &&
      Zlength(xs) == q && Zlength(ys) == q && Zlength(queries) == q &&
      (forall i, (0 <= i && i < n) => (2 <= periods[i] && periods[i] <= 6)) &&
      (forall i, (0 <= i && i < q) =>
        Znth(i, queries, pair(pair(0, 0), 0)) ==
          pair(pair(kinds[i], xs[i]), ys[i])) &&
      (forall i, (0 <= i && i < q) =>
        ((kinds[i] == 65 && 1 <= xs[i] && xs[i] < ys[i] && ys[i] <= n + 1) ||
         (kinds[i] == 67 && 1 <= xs[i] && xs[i] <= n &&
          2 <= ys[i] && ys[i] <= 6))) &&
      IntArray::seg(a, 1, n + 1, periods) * CharArray::full(type, q, kinds) *
      IntArray::full(qx, q, xs) * IntArray::full(qy, q, ys) *
      IntArray::undef_full(out, q) * IntArray::undef_seg(a_, 1, n + 1) *
      IntArray2::undef_full(seg, 400020, 60)
    Ensure
      exists (answers : list Z) (cells : list (list (option Z))),
        Spec(periods, queries, answers) &&
        __return == Zlength(answers) &&
        Zlength(cells) == 400020 &&
        (forall i, (0 <= i && i < 400020) =>
          Zlength(Znth(i, cells, nil)) == 60) &&
        IntArray::seg(a, 1, n + 1, periods) * CharArray::full(type, q, kinds) *
        IntArray::full(qx, q, xs) * IntArray::full(qy, q, ys) *
        IntArray::full(out, __return, answers) *
        IntArray::undef_seg(out, __return, q) *
        IntArray::seg_shape(a_, 1, n + 1) *
        IntArray2::mixed_full(seg, 400020, 60, cells)
*/
/* QCP_INSERT_END:shard09-P085-solver-contract */
{
    /*@ IntArray2::undef_full(seg, 400020, 60)
        which implies
        exists (cells0 : list (list (option Z))),
          CellsShaped(cells0) &&
          IntArray2::mixed_full(seg, 400020, 60, cells0)
    */
    /*@ Inv Assert
        exists (copied : list Z) (cells0 : list (list (option Z))),
          n == n@pre && q == q@pre && a == a@pre && type == type@pre &&
          qx == qx@pre && qy == qy@pre && out == out@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= q@pre && q@pre <= 100000 &&
          Zlength(periods) == n@pre &&
          Zlength(kinds) == q@pre && Zlength(xs) == q@pre &&
          Zlength(ys) == q@pre && Zlength(queries) == q@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (2 <= periods[j] && periods[j] <= 6)) &&
          PeriodsOK(periods) &&
          (forall j, (0 <= j && j < q@pre) =>
            Znth(j, queries, pair(pair(0, 0), 0)) ==
              pair(pair(kinds[j], xs[j]), ys[j])) &&
          (forall j, (0 <= j && j < q@pre) =>
            ((kinds[j] == 65 && 1 <= xs[j] && xs[j] < ys[j] &&
              ys[j] <= n@pre + 1) ||
             (kinds[j] == 67 && 1 <= xs[j] && xs[j] <= n@pre &&
              2 <= ys[j] && ys[j] <= 6))) &&
          1 <= i && i <= n@pre + 1 &&
          copied == NodeSlice(periods, 1, i - 1) &&
          CellsShaped(cells0) &&
          IntArray::seg(a, 1, n@pre + 1, periods) *
          IntArray::seg(a_, 1, i, copied) *
          IntArray::undef_seg(a_, i, n@pre + 1) *
          CharArray::full(type, q@pre, kinds) *
          IntArray::full(qx, q@pre, xs) * IntArray::full(qy, q@pre, ys) *
          IntArray::undef_full(out, q@pre) *
          IntArray2::mixed_full(seg, 400020, 60, cells0)
    */
    for (int i = 1; i <= n; i++)
        a_[i] = a[i];
    /*@ Assert
        exists (cells0 : list (list (option Z))),
          n == n@pre && q == q@pre && a == a@pre && type == type@pre &&
          qx == qx@pre && qy == qy@pre && out == out@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= q@pre && q@pre <= 100000 &&
          Zlength(periods) == n@pre &&
          Zlength(kinds) == q@pre && Zlength(xs) == q@pre &&
          Zlength(ys) == q@pre && Zlength(queries) == q@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (2 <= periods[j] && periods[j] <= 6)) &&
          PeriodsOK(periods) &&
          (forall j, (0 <= j && j < q@pre) =>
            Znth(j, queries, pair(pair(0, 0), 0)) ==
              pair(pair(kinds[j], xs[j]), ys[j])) &&
          (forall j, (0 <= j && j < q@pre) =>
            ((kinds[j] == 65 && 1 <= xs[j] && xs[j] < ys[j] &&
              ys[j] <= n@pre + 1) ||
             (kinds[j] == 67 && 1 <= xs[j] && xs[j] <= n@pre &&
              2 <= ys[j] && ys[j] <= 6))) &&
          CellsShaped(cells0) &&
          IntArray::seg(a, 1, n@pre + 1, periods) *
          IntArray::seg(a_, 1, n@pre + 1, periods) *
          CharArray::full(type, q@pre, kinds) *
          IntArray::full(qx, q@pre, xs) * IntArray::full(qy, q@pre, ys) *
          IntArray::undef_full(out, q@pre) *
          IntArray2::mixed_full(seg, 400020, 60, cells0)
    */
    build(1, 1, n) /*@ where arr = periods, n = n */;
    int nout = 0;
    /*@ Inv Assert
        exists (arr : list Z) (states : list (list Z)) (answers : list Z)
               (cells : list (list (option Z))),
          n == n@pre && q == q@pre && a == a@pre && type == type@pre &&
          qx == qx@pre && qy == qy@pre && out == out@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= q@pre && q@pre <= 100000 &&
          Zlength(periods) == n@pre &&
          Zlength(kinds) == q@pre && Zlength(xs) == q@pre &&
          Zlength(ys) == q@pre && Zlength(queries) == q@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (2 <= periods[j] && periods[j] <= 6)) &&
          PeriodsOK(periods) &&
          (forall j, (0 <= j && j < q@pre) =>
            Znth(j, queries, pair(pair(0, 0), 0)) ==
              pair(pair(kinds[j], xs[j]), ys[j])) &&
          (forall j, (0 <= j && j < q@pre) =>
            ((kinds[j] == 65 && 1 <= xs[j] && xs[j] < ys[j] &&
              ys[j] <= n@pre + 1) ||
             (kinds[j] == 67 && 1 <= xs[j] && xs[j] <= n@pre &&
              2 <= ys[j] && ys[j] <= 6))) &&
          0 <= i && i <= q@pre &&
          0 <= nout && nout <= i &&
          nout == AskCount(queries, i) &&
          Zlength(states) == i + 1 &&
          Znth(0, states, nil) == periods &&
          arr == Znth(i, states, nil) &&
          Zlength(arr) == n@pre && PeriodsOK(arr) &&
          Zlength(answers) == nout &&
          CellsShaped(cells) &&
          TreeOK(cells, arr, 1, 1, n@pre) &&
          QueryStepsOK(queries, states, i) &&
          AnswersOK(queries, states, answers, i) &&
          IntArray::seg(a, 1, n@pre + 1, periods) *
          CharArray::full(type, q@pre, kinds) *
          IntArray::full(qx, q@pre, xs) * IntArray::full(qy, q@pre, ys) *
          IntArray::full(out, nout, answers) *
          IntArray::undef_seg(out, nout, q@pre) *
          IntArray::seg(a_, 1, n@pre + 1, arr) *
          IntArray2::mixed_full(seg, 400020, 60, cells)
    */
    for (int i = 0; i < q; i++) {
        if (type[i] == 'C') {
            a_[qx[i]] = qy[i];
            update(1, 1, n, qx[i]) /*@ where n = n */;
        } else {
            out[nout] = query(1, 1, n, qx[i], qy[i] - 1, 0)
                          /*@ where n = n */;
            nout = nout + 1;
        }
    }
    return nout;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int a[MAXN];
//     for (int i = 1; i <= n; i++)
//         scanf("%d", &a[i]);
//     int q;
//     scanf("%d", &q);
//     static char type[MAXQ];
//     static int qx[MAXQ], qy[MAXQ], out[MAXQ];
//     for (int i = 0; i < q; i++) {
//         char c[4];
//         scanf("%1s %d %d", c, &qx[i], &qy[i]);
//         type[i] = c[0];
//     }
//     int nout = solver(n, a, q, type, qx, qy, out);
//     for (int i = 0; i < nout; i++)
//         printf("%d\n", out[i]);
//     return 0;
// }
