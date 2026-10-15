/* Codeforces 639/B - Bear and Forgotten Tree 3 */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P051_639B_bear_and_forgotten_tree_3.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> Z -> Z -> option (list (Z * Z)) -> Prop)
      (Feasible : Z -> Z -> Z -> Prop)
      (CanonicalEndpoints : Z -> Z -> Z -> Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P051_639B_bear_and_forgotten_tree_3_lib */
/* QCP_INSERT_END:P051_639B_bear_and_forgotten_tree_3.support */
static int solver(int n, int d, int h, int *eu, int *ev)
/* QCP_INSERT_BEGIN:P051_639B_bear_and_forgotten_tree_3.contract */

/*@
    Require
      2 <= n && n <= 100000 &&
      1 <= h && h <= d &&
      d <= n - 1 &&
      IntArray::undef_full(eu, n - 1) * IntArray::undef_full(ev, n - 1)
    Ensure
      ((__return == -1 && Spec(n, d, h, None) &&
        IntArray::undef_full(eu, n - 1) * IntArray::undef_full(ev, n - 1)) ||
       (exists edges eu_data ev_data,
          Spec(n, d, h, Some(edges)) && __return == Zlength(edges) &&
          (forall i, (0 <= i && i < Zlength(edges)) =>
            (eu_data[i] == fst(edges[i]) && ev_data[i] == snd(edges[i]))) &&
          IntArray::full(eu, Zlength(edges), eu_data) *
          IntArray::full(ev, Zlength(edges), ev_data)))
*/
/* QCP_INSERT_END:P051_639B_bear_and_forgotten_tree_3.contract */

{
    if (d > 2 * h || d < h || (d == 1 && n > 2)) {
        return -1;
    }

    /*@ Assert
          n == n@pre && d == d@pre && h == h@pre &&
          eu == eu@pre && ev == ev@pre &&
          2 <= n && n <= 100000 &&
          1 <= h && h <= d && d <= n - 1 &&
          Feasible(n, d, h) &&
          IntArray::undef_full(eu, n - 1) *
          IntArray::undef_full(ev, n - 1)
    */

    int count = 0;
    int next = 2;
    int last = 1;

    /*@ Inv Assert
          exists eu_data ev_data,
            n == n@pre && d == d@pre && h == h@pre &&
            eu == eu@pre && ev == ev@pre &&
            2 <= n && n <= 100000 &&
            1 <= h && h <= d && d <= n - 1 &&
            Feasible(n, d, h) &&
            0 <= i && i <= h &&
            count == i && next == i + 2 && last == i + 1 &&
            Zlength(eu_data) == count && Zlength(ev_data) == count &&
            (forall k, (0 <= k && k < count) =>
              CanonicalEndpoints(d, h, k, eu_data[k], ev_data[k])) &&
            IntArray::seg(eu, 0, count, eu_data) *
            IntArray::undef_seg(eu, count, n - 1) *
            IntArray::seg(ev, 0, count, ev_data) *
            IntArray::undef_seg(ev, count, n - 1)
    */
    for (int i = 0; i < h; ++i) {
        eu[count] = last;
        ev[count] = next;
        ++count;
        last = next;
        ++next;
    }

    last = 1;
    /*@ Inv Assert
          exists eu_data ev_data,
            n == n@pre && d == d@pre && h == h@pre &&
            eu == eu@pre && ev == ev@pre &&
            2 <= n && n <= 100000 &&
            1 <= h && h <= d && d <= n - 1 &&
            Feasible(n, d, h) &&
            0 <= i && i <= d - h &&
            count == h + i && next == h + i + 2 &&
            ((i == 0 && last == 1) ||
             (0 < i && last == h + i + 1)) &&
            Zlength(eu_data) == count && Zlength(ev_data) == count &&
            (forall k, (0 <= k && k < count) =>
              CanonicalEndpoints(d, h, k, eu_data[k], ev_data[k])) &&
            IntArray::seg(eu, 0, count, eu_data) *
            IntArray::undef_seg(eu, count, n - 1) *
            IntArray::seg(ev, 0, count, ev_data) *
            IntArray::undef_seg(ev, count, n - 1)
    */
    for (int i = 0; i < d - h; ++i) {
        eu[count] = last;
        ev[count] = next;
        ++count;
        last = next;
        ++next;
    }

    int attach = (d == h) ? 2 : 1;
    /*@ Inv Assert
          exists eu_data ev_data,
            n == n@pre && d == d@pre && h == h@pre &&
            eu == eu@pre && ev == ev@pre &&
            2 <= n && n <= 100000 &&
            1 <= h && h <= d && d <= n - 1 &&
            Feasible(n, d, h) &&
            d <= count && count <= n - 1 &&
            next == count + 2 &&
            ((d == h && last == 1) || (d != h && last == d + 1)) &&
            ((d == h && attach == 2) || (d != h && attach == 1)) &&
            Zlength(eu_data) == count && Zlength(ev_data) == count &&
            (forall k, (0 <= k && k < count) =>
              CanonicalEndpoints(d, h, k, eu_data[k], ev_data[k])) &&
            IntArray::seg(eu, 0, count, eu_data) *
            IntArray::undef_seg(eu, count, n - 1) *
            IntArray::seg(ev, 0, count, ev_data) *
            IntArray::undef_seg(ev, count, n - 1)
    */
    while (next <= n) {
        eu[count] = attach;
        ev[count] = next;
        ++count;
        ++next;
    }

    return count;
}

// int main(void)
// {
//     int n, d, h;
//     if (scanf("%d %d %d", &n, &d, &h) != 3) {
//         return 0;
//     }
//
//     int eu[100000];
//     int ev[100000];
//     int count = solver(n, d, h, eu, ev);
//     if (count < 0) {
//         puts("-1");
//         return 0;
//     }
//
//     for (int i = 0; i < count; ++i) {
//         printf("%d %d\n", eu[i], ev[i]);
//     }
//
//     return 0;
// }
