/* Codeforces 545/C - Woodcutters */
// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:P044_545C_woodcutters.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : list (Z*Z) -> Prop)
      (Spec : list (Z*Z) -> Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P044_545C_woodcutters_lib */
/* QCP_INSERT_END:P044_545C_woodcutters.support */
/*@ Extern Coq
      (PrefixFellingState : list (Z*Z) -> Z -> Z -> Z -> Prop)
*/
static int solver(const long long *x, const long long *h,
                  int n) /* QCP_INSERT_BEGIN:P044_545C_woodcutters.contract */

/*@ With (trees : list (Z*Z))
             (positions heights : list Z)
    Require
      1 <= Zlength(trees) && Zlength(trees) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(trees)) => ((1 <= fst(trees[i]) && fst(trees[i]) <= 1000000000) && (1 <= snd(trees[i]) && snd(trees[i]) <= 1000000000))) &&
      Pre(trees) &&
      n == Zlength(trees) &&
      Zlength(positions) == n && Zlength(heights) == n &&
      (forall i, (0 <= i && i < n) =>
        (fst(trees[i]) == positions[i] &&
         snd(trees[i]) == heights[i])) &&
      Int64Array::full(x, n, positions) *
      Int64Array::full(h, n, heights)
    Ensure
      Spec(trees, __return) &&
      Int64Array::full(x, n, positions) *
      Int64Array::full(h, n, heights)
*/
/* QCP_INSERT_END:P044_545C_woodcutters.contract */

{
    if (n <= 2)
        return n;
    int answer = 2;
    long long occupied = x[0];
    /*@ Inv Assert
          x == x@pre && h == h@pre && n == n@pre &&
          n@pre == Zlength(trees) &&
          3 <= n@pre && n@pre <= 100000 &&
          Zlength(positions) == n@pre &&
          Zlength(heights) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            ((1 <= fst(trees[j]) && fst(trees[j]) <= 1000000000) &&
             (1 <= snd(trees[j]) && snd(trees[j]) <= 1000000000))) &&
          Pre(trees) &&
          (forall j, (0 <= j && j < n@pre) =>
            (fst(trees[j]) == positions[j] &&
             snd(trees[j]) == heights[j])) &&
          1 <= i && i <= n@pre - 1 &&
          2 <= answer && answer <= i + 1 &&
          PrefixFellingState(trees, i, occupied, answer) &&
          Int64Array::full(x, n@pre, positions) *
          Int64Array::full(h, n@pre, heights)
    */
    for (int i = 1; i + 1 < n; ++i)
    {
        if (x[i] - h[i] > occupied)
        {
            ++answer;
            occupied = x[i];
        }
        else if (x[i] + h[i] < x[i + 1])
        {
            ++answer;
            occupied = x[i] + h[i];
        }
        else
            occupied = x[i];
    }
    return answer;
}

// int main(void)
// {
//     int n; if (scanf("%d", &n) != 1) return 0;
//     long long *x = malloc((size_t)n * sizeof(*x)), *h = malloc((size_t)n * sizeof(*h));
//     for (int i = 0; i < n; ++i) scanf("%lld %lld", &x[i], &h[i]);
//     printf("%d\n", solver(x, h, n)); free(x); free(h);
//     return 0;
// }
