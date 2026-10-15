/* Codeforces 1955/D - Inaccurate Subsequence Search */
// #include <stdio.h>
// #include <stdlib.h>

#define MAXA 1000000
static int need[MAXA + 1], have[MAXA + 1];

/*@ Extern Coq (z_min : Z -> Z -> Z) */
static int minimum(int a, int b)
/*@ Require emp
    Ensure __return == z_min(a, b) && emp
*/
{
    return a < b ? a : b;
}

/* QCP_INSERT_BEGIN:P039_1955D_inaccurate_subsequence_search.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P039_1955D_inaccurate_subsequence_search_lib */
/* QCP_INSERT_END:P039_1955D_inaccurate_subsequence_search.support */
/*@ Extern Coq
      (FrequencyTable : list Z -> list Z -> Prop)
      (TableMatchScore : list Z -> list Z -> Z -> Prop)
      (CountedGoodWindows : Z -> list Z -> list Z -> Z -> Z -> Prop)
      (ClearedByPrefix : list Z -> list Z -> Z -> list Z -> Prop)
*/
static int solver(const int *a, int n, const int *b, int m, int k)/* QCP_INSERT_BEGIN:P039_1955D_inaccurate_subsequence_search.contract */

/*@ With (values : list Z)
             (b_data : list Z)
    Require
      1 <= k && k <= Zlength(b_data) &&
      Zlength(b_data) <= Zlength(values) &&
      Zlength(values) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 1000000)) &&
      (forall i, (0 <= i && i < Zlength(b_data)) => (1 <= b_data[i] && b_data[i] <= 1000000)) &&
      n == Zlength(values) && m == Zlength(b_data) &&
      IntArray::full(a, n, values) * IntArray::full(b, m, b_data) *
      IntArray::full(need, 1000001, repeat_Z(0, 1000001)) *
      IntArray::full(have, 1000001, repeat_Z(0, 1000001))
    Ensure
      Spec(k, values, b_data, __return) &&
      IntArray::full(a, n, values) * IntArray::full(b, m, b_data) *
      IntArray::full(need, 1000001, repeat_Z(0, 1000001)) *
      IntArray::full(have, 1000001, repeat_Z(0, 1000001))
*/
/* QCP_INSERT_END:P039_1955D_inaccurate_subsequence_search.contract */

{
    /*@ Inv Assert
          exists need_data,
            a == a@pre && n == n@pre &&
            b == b@pre && m == m@pre && k == k@pre &&
            1 <= k@pre && k@pre <= Zlength(b_data) &&
            Zlength(b_data) <= Zlength(values) &&
            Zlength(values) <= 200000 &&
            (forall j, (0 <= j && j < Zlength(values)) =>
              (1 <= values[j] && values[j] <= 1000000)) &&
            (forall j, (0 <= j && j < Zlength(b_data)) =>
              (1 <= b_data[j] && b_data[j] <= 1000000)) &&
            n@pre == Zlength(values) && m@pre == Zlength(b_data) &&
            0 <= i && i <= m@pre &&
            FrequencyTable(sublist(0, i, b_data), need_data) &&
            IntArray::full(a, n@pre, values) *
            IntArray::full(b, m@pre, b_data) *
            IntArray::full(need, 1000001, need_data) *
            IntArray::full(have, 1000001, repeat_Z(0, 1000001))
     */
    for (int i = 0; i < m; ++i) {
        ++need[b[i]];
    }

    int matched = 0, answer = 0;
    /*@ Inv Assert
          exists need_data have_data,
            a == a@pre && n == n@pre &&
            b == b@pre && m == m@pre && k == k@pre &&
            1 <= k@pre && k@pre <= Zlength(b_data) &&
            Zlength(b_data) <= Zlength(values) &&
            Zlength(values) <= 200000 &&
            (forall j, (0 <= j && j < Zlength(values)) =>
              (1 <= values[j] && values[j] <= 1000000)) &&
            (forall j, (0 <= j && j < Zlength(b_data)) =>
              (1 <= b_data[j] && b_data[j] <= 1000000)) &&
            n@pre == Zlength(values) && m@pre == Zlength(b_data) &&
            0 <= i && i <= m@pre &&
            0 <= matched && matched <= i &&
            answer == 0 &&
            FrequencyTable(b_data, need_data) &&
            FrequencyTable(sublist(0, i, values), have_data) &&
            TableMatchScore(need_data, have_data, matched) &&
            IntArray::full(a, n@pre, values) *
            IntArray::full(b, m@pre, b_data) *
            IntArray::full(need, 1000001, need_data) *
            IntArray::full(have, 1000001, have_data)
     */
    for (int i = 0; i < m; ++i) {
        int v = a[i];
        matched -= minimum(have[v], need[v]);
        ++have[v];
        matched += minimum(have[v], need[v]);
    }

    if (matched >= k) {
        ++answer;
    }

    /*@ Inv Assert
          exists need_data have_data,
            a == a@pre && n == n@pre &&
            b == b@pre && m == m@pre && k == k@pre &&
            1 <= k@pre && k@pre <= Zlength(b_data) &&
            Zlength(b_data) <= Zlength(values) &&
            Zlength(values) <= 200000 &&
            (forall j, (0 <= j && j < Zlength(values)) =>
              (1 <= values[j] && values[j] <= 1000000)) &&
            (forall j, (0 <= j && j < Zlength(b_data)) =>
              (1 <= b_data[j] && b_data[j] <= 1000000)) &&
            n@pre == Zlength(values) && m@pre == Zlength(b_data) &&
            m@pre <= i && i <= n@pre &&
            0 <= matched && matched <= m@pre &&
            0 <= answer && answer <= i - m@pre + 1 &&
            FrequencyTable(b_data, need_data) &&
            FrequencyTable(sublist(i - m@pre, i, values), have_data) &&
            TableMatchScore(need_data, have_data, matched) &&
            CountedGoodWindows(k@pre, values, b_data,
              i - m@pre + 1, answer) &&
            IntArray::full(a, n@pre, values) *
            IntArray::full(b, m@pre, b_data) *
            IntArray::full(need, 1000001, need_data) *
            IntArray::full(have, 1000001, have_data)
     */
    for (int i = m; i < n; ++i) {
        int v = a[i - m];
        matched -= minimum(have[v], need[v]);
        --have[v];
        matched += minimum(have[v], need[v]);

        v = a[i];
        matched -= minimum(have[v], need[v]);
        ++have[v];
        matched += minimum(have[v], need[v]);

        if (matched >= k) {
            ++answer;
        }
    }

    /*@ Inv Assert
          exists need_data original_have have_data,
            a == a@pre && n == n@pre &&
            b == b@pre && m == m@pre && k == k@pre &&
            1 <= k@pre && k@pre <= Zlength(b_data) &&
            Zlength(b_data) <= Zlength(values) &&
            Zlength(values) <= 200000 &&
            (forall j, (0 <= j && j < Zlength(values)) =>
              (1 <= values[j] && values[j] <= 1000000)) &&
            (forall j, (0 <= j && j < Zlength(b_data)) =>
              (1 <= b_data[j] && b_data[j] <= 1000000)) &&
            n@pre == Zlength(values) && m@pre == Zlength(b_data) &&
            0 <= i && i <= n@pre &&
            0 <= matched && matched <= m@pre &&
            0 <= answer && answer <= n@pre - m@pre + 1 &&
            FrequencyTable(b_data, need_data) &&
            FrequencyTable(sublist(n@pre - m@pre, n@pre, values), original_have) &&
            ClearedByPrefix(original_have, values, i, have_data) &&
            TableMatchScore(need_data, original_have, matched) &&
            CountedGoodWindows(k@pre, values, b_data,
              n@pre - m@pre + 1, answer) &&
            IntArray::full(a, n@pre, values) *
            IntArray::full(b, m@pre, b_data) *
            IntArray::full(need, 1000001, need_data) *
            IntArray::full(have, 1000001, have_data)
     */
    for (int i = 0; i < n; ++i) {
        have[a[i]] = 0;
    }
    /*@ Inv Assert
          exists original_need need_data,
            a == a@pre && n == n@pre &&
            b == b@pre && m == m@pre && k == k@pre &&
            1 <= k@pre && k@pre <= Zlength(b_data) &&
            Zlength(b_data) <= Zlength(values) &&
            Zlength(values) <= 200000 &&
            (forall j, (0 <= j && j < Zlength(values)) =>
              (1 <= values[j] && values[j] <= 1000000)) &&
            (forall j, (0 <= j && j < Zlength(b_data)) =>
              (1 <= b_data[j] && b_data[j] <= 1000000)) &&
            n@pre == Zlength(values) && m@pre == Zlength(b_data) &&
            0 <= i && i <= m@pre &&
            0 <= matched && matched <= m@pre &&
            0 <= answer && answer <= n@pre - m@pre + 1 &&
            FrequencyTable(b_data, original_need) &&
            ClearedByPrefix(original_need, b_data, i, need_data) &&
            CountedGoodWindows(k@pre, values, b_data,
              n@pre - m@pre + 1, answer) &&
            IntArray::full(a, n@pre, values) *
            IntArray::full(b, m@pre, b_data) *
            IntArray::full(need, 1000001, need_data) *
            IntArray::full(have, 1000001, repeat_Z(0, 1000001))
     */
    for (int i = 0; i < m; ++i) {
        need[b[i]] = 0;
    }

    return answer;
}

// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--) {
//         int n, m, k;
//         scanf("%d %d %d", &n, &m, &k);
//         int *a = malloc((size_t)n * sizeof(*a));
//         int *b = malloc((size_t)m * sizeof(*b));
//         for (int i = 0; i < n; ++i) {
//             scanf("%d", &a[i]);
//         }
//         for (int i = 0; i < m; ++i) {
//             scanf("%d", &b[i]);
//         }
//         printf("%d\n", solver(a, n, b, m, k));
//         free(a);
//         free(b);
//     }
//     return 0;
// }
