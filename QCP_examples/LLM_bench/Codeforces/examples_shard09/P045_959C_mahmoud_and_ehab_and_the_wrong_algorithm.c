/*
 * Codeforces 959/C - Mahmoud and Ehab and the wrong algorithm
 * (rating 1500, CONSTRUCTIVE)
 *
 * Section 2 (algorithm correct): the star centred at 1 has evenCnt = 1, which
 * is also the true cover size.
 *
 * Section 1 (algorithm wrong): a double star.  Centres 1 and 2 are adjacent,
 * each carrying at least two leaves; the true cover is {1, 2} of size 2 while
 * both depth classes hold at least three nodes, so the algorithm answers >= 3.
 * That needs n >= 6; for smaller n no counterexample exists.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> option(list (Z * Z)) * option(list (Z * Z)) -> Prop)
*/
/*@ Extern Coq (fst : {A B}  -> A * B -> A) */
/*@ Extern Coq (snd : {A B} -> A * B -> B) */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P045_959C_mahmoud_and_ehab_and_the_wrong_algorithm_lib */

/* solver: pure.  Writes the counterexample tree's n-1 edges into eu/ev and
 * returns 1, or returns 0 when no counterexample exists. */
static int solver(int n, int *eu, int *ev)
/* QCP_INSERT_BEGIN:shard09-P045-solver-contract */
/*@ Require
      2 <= n && n <= 100000 &&
      IntArray::undef_full(eu, n - 1) * IntArray::undef_full(ev, n - 1)
    Ensure
      exists (out : option(list (Z * Z)) * option(list (Z * Z))),
        Spec(n@pre, out) &&
        ((fst(out) == None && __return == 0 && IntArray::undef_full(eu, n - 1) * IntArray::undef_full(ev, n - 1)) || 
        (exists (edges : list(Z*Z)), fst(out) == Some(edges) && __return == 1 && Zlength(edges) == n - 1 && exists (us : list Z) (vs : list Z), Zlength(us) == n - 1 && Zlength(vs) == n - 1 && (forall i, (0 <= i && i < n - 1) => us[i] == fst(edges[i]) && vs[i] == snd(edges[i])) && IntArray::full(eu, n - 1, us) * IntArray::full(ev, n - 1, vs)))
*/
/* QCP_INSERT_END:shard09-P045-solver-contract */
{
    if (n < 6)
        return 0;
    int m = 0;
    { eu[m] = 1; ev[m] = 2; m++; } /* the two centres */
    { eu[m] = 1; ev[m] = 3; m++; } /* two leaves on centre 1 */
    { eu[m] = 1; ev[m] = 4; m++; }
    { eu[m] = 2; ev[m] = 5; m++; } /* two leaves on centre 2 */
    { eu[m] = 2; ev[m] = 6; m++; }
    /*@ Inv Assert
      n == n@pre && eu == eu@pre && ev == ev@pre &&
      6 <= n@pre && n@pre <= 100000 &&
      7 <= v && v <= n@pre + 1 &&
      m == v - 2 &&
      exists (us : list Z) (vs : list Z),
        Zlength(us) == m && Zlength(vs) == m &&
        (forall i, (0 <= i && i < m) =>
          (((i == 3 || i == 4) => us[i] == 2) &&
           ((i != 3 && i != 4) => us[i] == 1) &&
           vs[i] == i + 2)) &&
        IntArray::seg(eu, 0, m, us) * IntArray::undef_seg(eu, m, n@pre - 1) *
        IntArray::seg(ev, 0, m, vs) * IntArray::undef_seg(ev, m, n@pre - 1)
    */
    for (int v = 7; v <= n; v++) {        /* the rest keeps both sides big */
        eu[m] = 1;
        { ev[m] = v; m++; }
    }
    return 1;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int eu[100005], ev[100005];
//     if (solver(n, eu, ev))
//         for (int i = 0; i < n - 1; i++)
//             printf("%d %d\n", eu[i], ev[i]);
//     else
//         puts("-1");
//     for (int v = 2; v <= n; v++)          /* section 2: star centred at 1 */
//         printf("1 %d\n", v);
//     return 0;
// }
