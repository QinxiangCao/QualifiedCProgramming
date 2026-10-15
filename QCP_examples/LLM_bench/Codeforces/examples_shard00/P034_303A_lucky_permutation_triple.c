/* Codeforces 303/A - Lucky Permutation Triple */
// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:P034_303A_lucky_permutation_triple.support */
/*@ Extern Coq
      (pair : {A} {B} -> A -> B -> A * B)
      (Spec : Z -> option (list Z * list Z * list Z) -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P034_303A_lucky_permutation_triple_lib */
/* QCP_INSERT_END:P034_303A_lucky_permutation_triple.support */
/*@ Extern Coq
      (IdentityRange : Z -> list Z -> Prop)
      (TwiceModRange : Z -> Z -> list Z -> Prop)
*/
static int solver(int n, int *out)/* QCP_INSERT_BEGIN:P034_303A_lucky_permutation_triple.contract */

/*@
    Require
      1 <= n && n <= 100000 &&
      IntArray::undef_full(out, 3 * n)
    Ensure
      ((__return == 0 && Spec(n, None) && IntArray::undef_full(out, 3 * n)) ||
       (exists a b c,
        __return == 1 && Spec(n, Some(pair(pair(a, b), c))) &&
          IntArray::full(out, 3 * n, app(a, app(b, c)))))
*/
/* QCP_INSERT_END:P034_303A_lucky_permutation_triple.contract */

{
    if ((n & 1) == 0) return 0;
    /*@ Inv Assert
      exists (a : list Z),
        n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 100000 && n@pre % 2 == 1 &&
        0 <= i && i <= n@pre &&
        IdentityRange(i, a) &&
        IntArray::seg(out, 0, i, a) *
        IntArray::undef_seg(out, i, 3 * n@pre)
    */
    for (int i = 0; i < n; ++i) out[i] = i;
    /*@ Inv Assert
      exists (a : list Z) (b : list Z),
        n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 100000 && n@pre % 2 == 1 &&
        0 <= i && i <= n@pre &&
        IdentityRange(n@pre, a) && IdentityRange(i, b) &&
        IntArray::seg(out, 0, n@pre, a) *
        IntArray::seg(out, n@pre, n@pre + i, b) *
        IntArray::undef_seg(out, n@pre + i, 3 * n@pre)
    */
    for (int i = 0; i < n; ++i) out[n + i] = i;
    /*@ Inv Assert
      exists (a : list Z) (b : list Z) (c : list Z),
        n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 100000 && n@pre % 2 == 1 &&
        0 <= i && i <= n@pre &&
        IdentityRange(n@pre, a) && IdentityRange(n@pre, b) &&
        TwiceModRange(n@pre, i, c) &&
        IntArray::seg(out, 0, n@pre, a) *
        IntArray::seg(out, n@pre, 2 * n@pre, b) *
        IntArray::seg(out, 2 * n@pre, 2 * n@pre + i, c) *
        IntArray::undef_seg(out, 2 * n@pre + i, 3 * n@pre)
    */
    for (int i = 0; i < n; ++i) out[2 * n + i] = 2 * i % n;
    return 1;
}

// int main(void)
// {
//     int n; if (scanf("%d", &n) != 1) return 0;
//     int *out = malloc((size_t)3 * n * sizeof(*out));
//     if (!solver(n, out)) { puts("-1"); free(out); return 0; }
//     for (int row = 0; row < 3; ++row)
//         for (int i = 0; i < n; ++i) printf("%d%c", out[row * n + i], i + 1 == n ? '\n' : ' ');
//     free(out); return 0;
// }
