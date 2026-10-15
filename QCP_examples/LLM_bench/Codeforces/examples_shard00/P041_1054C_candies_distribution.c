/* Codeforces 1054/C - Candies Distribution */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P041_1054C_candies_distribution.support */
/*@ Extern Coq
      (Spec : list Z -> list Z -> option (list Z) -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P041_1054C_candies_distribution_lib */
/* QCP_INSERT_END:P041_1054C_candies_distribution.support */
/*@ Extern Coq
      (CandyCandidatePrefix : Z -> list Z -> list Z -> Z -> list Z -> Prop)
      (CandyLeftCount : list Z -> Z -> Z -> Z -> Prop)
      (CandyRightCount : list Z -> Z -> Z -> Z -> Prop)
      (CandyCheckedPrefix : list Z -> list Z -> list Z -> Z -> Prop)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
static int solver(int n, const int *l, const int *r, int *a)/* QCP_INSERT_BEGIN:P041_1054C_candies_distribution.contract */

/*@ With (l_data : list Z)
             (r_data : list Z)
    Require
      1 <= Zlength(l_data) && Zlength(l_data) <= 1000 &&
      Zlength(r_data) == Zlength(l_data) &&
      (forall i, (0 <= i && i < Zlength(l_data)) => (0 <= l_data[i] && l_data[i] <= Zlength(l_data))) &&
      (forall i, (0 <= i && i < Zlength(r_data)) => (0 <= r_data[i] && r_data[i] <= Zlength(l_data))) &&
      n == Zlength(l_data) &&
      IntArray::full(l, n, l_data) * IntArray::full(r, n, r_data) *
      IntArray::undef_full(a, n)
    Ensure
      IntArray::full(l, n, l_data) * IntArray::full(r, n, r_data) *
      (((__return == 0 && Spec(l_data, r_data, None)) &&
        exists post, IntArray::full(a, n, post)) ||
       (exists result,
          __return == 1 && Spec(l_data, r_data, Some(result)) &&
          IntArray::full(a, n, result)))
*/
/* QCP_INSERT_END:P041_1054C_candies_distribution.contract */

{
    /*@ Inv Assert
      exists prefix,
        n == n@pre && l == l@pre && r == r@pre && a == a@pre &&
        n@pre == Zlength(l_data) &&
        1 <= n@pre && n@pre <= 1000 &&
        Zlength(r_data) == n@pre &&
        (forall k, (0 <= k && k < n@pre) =>
          (0 <= l_data[k] && l_data[k] <= n@pre)) &&
        (forall k, (0 <= k && k < n@pre) =>
          (0 <= r_data[k] && r_data[k] <= n@pre)) &&
        0 <= i && i <= n@pre &&
        CandyCandidatePrefix(n@pre, l_data, r_data, i, prefix) &&
        IntArray::full(l, n@pre, l_data) *
        IntArray::full(r, n@pre, r_data) *
        IntArray::seg(a, 0, i, prefix) *
        IntArray::undef_seg(a, i, n@pre)
    */
    for (int i = 0; i < n; ++i) a[i] = n - l[i] - r[i];
    /*@ Inv Assert
      exists candidate,
        n == n@pre && l == l@pre && r == r@pre && a == a@pre &&
        n@pre == Zlength(l_data) &&
        1 <= n@pre && n@pre <= 1000 &&
        Zlength(r_data) == n@pre &&
        (forall k, (0 <= k && k < n@pre) =>
          (0 <= l_data[k] && l_data[k] <= n@pre)) &&
        (forall k, (0 <= k && k < n@pre) =>
          (0 <= r_data[k] && r_data[k] <= n@pre)) &&
        CandyCandidatePrefix(n@pre, l_data, r_data, n@pre, candidate) &&
        0 <= i && i <= n@pre &&
        CandyCheckedPrefix(l_data, r_data, candidate, i) &&
        IntArray::full(l, n@pre, l_data) *
        IntArray::full(r, n@pre, r_data) *
        IntArray::full(a, n@pre, candidate)
    */
    for (int i = 0; i < n; ++i) {
        int cl = 0, cr = 0;
        /*@ Inv Assert
          exists candidate,
            n == n@pre && l == l@pre && r == r@pre && a == a@pre &&
            n@pre == Zlength(l_data) &&
            1 <= n@pre && n@pre <= 1000 &&
            Zlength(r_data) == n@pre &&
            (forall k, (0 <= k && k < n@pre) =>
              (0 <= l_data[k] && l_data[k] <= n@pre)) &&
            (forall k, (0 <= k && k < n@pre) =>
              (0 <= r_data[k] && r_data[k] <= n@pre)) &&
            CandyCandidatePrefix(n@pre, l_data, r_data, n@pre, candidate) &&
            0 <= i && i < n@pre &&
            0 <= j && j <= i &&
            0 <= cl && cl <= j && cr == 0 &&
            CandyCheckedPrefix(l_data, r_data, candidate, i) &&
            CandyLeftCount(candidate, i, j, cl) &&
            IntArray::full(l, n@pre, l_data) *
            IntArray::full(r, n@pre, r_data) *
            IntArray::full(a, n@pre, candidate)
        */
        for (int j = 0; j < i; ++j) cl += a[j] > a[i];
        /*@ Inv Assert
          exists candidate,
            n == n@pre && l == l@pre && r == r@pre && a == a@pre &&
            n@pre == Zlength(l_data) &&
            1 <= n@pre && n@pre <= 1000 &&
            Zlength(r_data) == n@pre &&
            (forall k, (0 <= k && k < n@pre) =>
              (0 <= l_data[k] && l_data[k] <= n@pre)) &&
            (forall k, (0 <= k && k < n@pre) =>
              (0 <= r_data[k] && r_data[k] <= n@pre)) &&
            CandyCandidatePrefix(n@pre, l_data, r_data, n@pre, candidate) &&
            0 <= i && i < n@pre &&
            i + 1 <= j && j <= n@pre &&
            0 <= cl && cl <= i &&
            0 <= cr && cr <= j - (i + 1) &&
            CandyCheckedPrefix(l_data, r_data, candidate, i) &&
            CandyLeftCount(candidate, i, i, cl) &&
            CandyRightCount(candidate, i, j, cr) &&
            IntArray::full(l, n@pre, l_data) *
            IntArray::full(r, n@pre, r_data) *
            IntArray::full(a, n@pre, candidate)
        */
        for (int j = i + 1; j < n; ++j) cr += a[j] > a[i];
        if (a[i] < 1 || cl != l[i] || cr != r[i]) return 0;
    }
    return 1;
}

// int main(void)
// {
//     int n, l[1000], r[1000], a[1000];
//     if (scanf("%d", &n) != 1) return 0;
//     for (int i = 0; i < n; ++i) scanf("%d", &l[i]);
//     for (int i = 0; i < n; ++i) scanf("%d", &r[i]);
//     if (!solver(n, l, r, a)) { puts("NO"); return 0; }
//     puts("YES");
//     for (int i = 0; i < n; ++i) printf("%d%c", a[i], i + 1 == n ? '\n' : ' ');
//     return 0;
// }
