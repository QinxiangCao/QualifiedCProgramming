/*
 * Codeforces 509/E - Pretty Song  (rating 2000, MATH)
 *
 * Group the substrings by length L: their total vowel count is
 * sum_{i=L..n} p_i - sum_{i=0..n-L} p_i, where p is the vowel prefix count.
 * Prefix sums of p make each length O(1), and each contributes that total / L.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P070-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P070_509E_pretty_song_lib */
/*@ Extern Coq (R :: *) */
/*@ Extern Coq
      (Spec : list Z -> R -> Prop)
      (PrettyTerms : list Z -> list Z -> R -> Prop)
*/
/* QCP_INSERT_END:shard09-P070-solver-support */

/*@ Extern Coq
      (VowelPrefixCounts : list Z -> list Z -> Prop)
      (PrefixCountTotals : list Z -> list Z -> Prop)
      (PrettyTermPrefix : list Z -> list Z -> Prop)
*/

/* solver: exact whole-case representation.  term[L-1] is the integer total
 * number of vowels over all substrings of length L.  The mathematical result
 * is exactly sum term[L-1]/L; no floating-point value crosses the contract. */
static void solver(const char *s, int n, long long *term,
                   long long *pre, long long *pp)
/* QCP_INSERT_BEGIN:shard09-P070-normalized-solver-contract */
/*@ With (text : list Z)
    Require
      1 <= n && n <= 500000 && (forall i, (0 <= i && i < n) => (65 <= text[i] && text[i] <= 90)) && n == Zlength(text) && CharArray::full(s, n, text) * Int64Array::full_shape(term, n) * Int64Array::full_shape(pre, n + 1) * Int64Array::full_shape(pp, n + 1)
    Ensure
      exists (terms : list Z) (real_out : R), Spec(text, real_out) && PrettyTerms(text, terms, real_out) && CharArray::full(s, n, text) * Int64Array::full(term, n, terms) * Int64Array::full_shape(pre, n + 1) * Int64Array::full_shape(pp, n + 1)
*/
/* QCP_INSERT_END:shard09-P070-normalized-solver-contract */
{
    /*@ Assert
          exists (old_pre0 : Z),
          s == s@pre && n == n@pre && term == term@pre &&
          pre == pre@pre && pp == pp@pre &&
          1 <= n@pre && n@pre <= 500000 &&
          n@pre == Zlength(text) &&
          (forall k, (0 <= k && k < n@pre) =>
             (65 <= text[k] && text[k] <= 90)) &&
          CharArray::full(s@pre, n@pre, text) *
          Int64Array::full_shape(term@pre, n@pre) *
          data_at(pre@pre + 0 * sizeof(long long), long long, old_pre0) *
          Int64Array::missing_i_shape(pre@pre, 0, 0, n@pre + 1) *
          Int64Array::full_shape(pp@pre, n@pre + 1)
    */
    pre[0] = 0;
    /*@ Inv Assert
          exists (pre_values : list Z),
          s == s@pre && n == n@pre && term == term@pre &&
          pre == pre@pre && pp == pp@pre &&
          1 <= n@pre && n@pre <= 500000 &&
          n@pre == Zlength(text) &&
          (forall k, (0 <= k && k < n@pre) =>
             (65 <= text[k] && text[k] <= 90)) &&
          0 <= i && i <= n@pre && Zlength(pre_values) == i + 1 &&
          (forall k, (0 <= k && k < i + 1) =>
             (0 <= pre_values[k] && pre_values[k] <= k)) &&
          VowelPrefixCounts(text, pre_values) &&
          CharArray::full(s@pre, n@pre, text) *
          Int64Array::full_shape(term@pre, n@pre) *
          Int64Array::seg(pre@pre, 0, i + 1, pre_values) *
          Int64Array::seg_shape(pre@pre, i + 1, n@pre + 1) *
          Int64Array::full_shape(pp@pre, n@pre + 1)
    */
    for (int i = 0; i < n; i++) {
        /*@ Assert
              exists (pre_values : list Z) (old_next : Z),
              s == s@pre && n == n@pre && term == term@pre &&
              pre == pre@pre && pp == pp@pre &&
              1 <= n@pre && n@pre <= 500000 &&
              n@pre == Zlength(text) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (65 <= text[k] && text[k] <= 90)) &&
              0 <= i && i < n@pre && Zlength(pre_values) == i + 1 &&
              (forall k, (0 <= k && k < i + 1) =>
                 (0 <= pre_values[k] && pre_values[k] <= k)) &&
              VowelPrefixCounts(text, pre_values) &&
              CharArray::full(s@pre, n@pre, text) *
              Int64Array::full_shape(term@pre, n@pre) *
              Int64Array::seg(pre@pre, 0, i + 1, pre_values) *
              data_at(pre@pre + (i + 1) * sizeof(long long),
                      long long, old_next) *
              Int64Array::missing_i_shape(pre@pre, i + 1, i + 1,
                                          n@pre + 1) *
              Int64Array::full_shape(pp@pre, n@pre + 1)
        */
        char c = s[i];
        int v = (c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U' ||
                 c == 'Y');
        pre[i + 1] = pre[i] + v;
    }
    /*@ Assert
          exists (pre_values : list Z) (old_pp0 : Z),
          s == s@pre && n == n@pre && term == term@pre &&
          pre == pre@pre && pp == pp@pre &&
          1 <= n@pre && n@pre <= 500000 &&
          n@pre == Zlength(text) &&
          (forall k, (0 <= k && k < n@pre) =>
             (65 <= text[k] && text[k] <= 90)) &&
          Zlength(pre_values) == n@pre + 1 &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (0 <= pre_values[k] && pre_values[k] <= k)) &&
          VowelPrefixCounts(text, pre_values) &&
          CharArray::full(s@pre, n@pre, text) *
          Int64Array::full_shape(term@pre, n@pre) *
          data_at(pre@pre + 0 * sizeof(long long), long long,
                  pre_values[0]) *
          Int64Array::missing_i(pre@pre, 0, 0, n@pre + 1, pre_values) *
          data_at(pp@pre + 0 * sizeof(long long), long long, old_pp0) *
          Int64Array::missing_i_shape(pp@pre, 0, 0, n@pre + 1)
    */
    pp[0] = pre[0];
    /*@ Assert
          exists (pre_values : list Z) (pp_values : list Z),
          s == s@pre && n == n@pre && term == term@pre &&
          pre == pre@pre && pp == pp@pre &&
          1 <= n@pre && n@pre <= 500000 &&
          n@pre == Zlength(text) &&
          (forall k, (0 <= k && k < n@pre) =>
             (65 <= text[k] && text[k] <= 90)) &&
          Zlength(pre_values) == n@pre + 1 &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (0 <= pre_values[k] && pre_values[k] <= k)) &&
          Zlength(pp_values) == 1 && pp_values[0] == pre_values[0] &&
          VowelPrefixCounts(text, pre_values) &&
          PrefixCountTotals(pre_values, pp_values) &&
          CharArray::full(s@pre, n@pre, text) *
          Int64Array::full_shape(term@pre, n@pre) *
          Int64Array::full(pre@pre, n@pre + 1, pre_values) *
          Int64Array::seg(pp@pre, 0, 1, pp_values) *
          Int64Array::seg_shape(pp@pre, 1, n@pre + 1)
    */
    /*@ Inv Assert
          exists (pre_values : list Z) (pp_values : list Z),
          s == s@pre && n == n@pre && term == term@pre &&
          pre == pre@pre && pp == pp@pre &&
          1 <= n@pre && n@pre <= 500000 &&
          n@pre == Zlength(text) &&
          (forall k, (0 <= k && k < n@pre) =>
             (65 <= text[k] && text[k] <= 90)) &&
          1 <= i && i <= n@pre + 1 &&
          Zlength(pre_values) == n@pre + 1 && Zlength(pp_values) == i &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (0 <= pre_values[k] && pre_values[k] <= k)) &&
          (forall k, (0 <= k && k < i) =>
             (0 <= pp_values[k] && pp_values[k] <= k * (k + 1) / 2)) &&
          VowelPrefixCounts(text, pre_values) &&
          PrefixCountTotals(pre_values, pp_values) &&
          CharArray::full(s@pre, n@pre, text) *
          Int64Array::full_shape(term@pre, n@pre) *
          Int64Array::full(pre@pre, n@pre + 1, pre_values) *
          Int64Array::seg(pp@pre, 0, i, pp_values) *
          Int64Array::seg_shape(pp@pre, i, n@pre + 1)
    */
    for (int i = 1; i <= n; i++)
        /*@ Assert
              exists (pre_values : list Z) (pp_values : list Z)
                     (old_next : Z),
              s == s@pre && n == n@pre && term == term@pre &&
              pre == pre@pre && pp == pp@pre &&
              1 <= n@pre && n@pre <= 500000 &&
              n@pre == Zlength(text) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (65 <= text[k] && text[k] <= 90)) &&
              1 <= i && i <= n@pre &&
              Zlength(pre_values) == n@pre + 1 &&
              Zlength(pp_values) == i &&
              (forall k, (0 <= k && k < n@pre + 1) =>
                 (0 <= pre_values[k] && pre_values[k] <= k)) &&
              (forall k, (0 <= k && k < i) =>
                 (0 <= pp_values[k] &&
                  pp_values[k] <= k * (k + 1) / 2)) &&
              VowelPrefixCounts(text, pre_values) &&
              PrefixCountTotals(pre_values, pp_values) &&
              CharArray::full(s@pre, n@pre, text) *
              Int64Array::full_shape(term@pre, n@pre) *
              Int64Array::full(pre@pre, n@pre + 1, pre_values) *
              Int64Array::seg(pp@pre, 0, i, pp_values) *
              data_at(pp@pre + i * sizeof(long long), long long, old_next) *
              Int64Array::missing_i_shape(pp@pre, i, i, n@pre + 1)
        */
        pp[i] = pp[i - 1] + pre[i];       /* prefix sums of the prefix counts */
    /*@ Assert
          exists (pre_values : list Z) (pp_values : list Z),
          s == s@pre && n == n@pre && term == term@pre &&
          pre == pre@pre && pp == pp@pre &&
          1 <= n@pre && n@pre <= 500000 &&
          n@pre == Zlength(text) &&
          (forall k, (0 <= k && k < n@pre) =>
             (65 <= text[k] && text[k] <= 90)) &&
          Zlength(pre_values) == n@pre + 1 &&
          Zlength(pp_values) == n@pre + 1 &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (0 <= pre_values[k] && pre_values[k] <= k)) &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (0 <= pp_values[k] && pp_values[k] <= k * (k + 1) / 2)) &&
          VowelPrefixCounts(text, pre_values) &&
          PrefixCountTotals(pre_values, pp_values) &&
          CharArray::full(s@pre, n@pre, text) *
          Int64Array::full_shape(term@pre, n@pre) *
          Int64Array::full(pre@pre, n@pre + 1, pre_values) *
          Int64Array::full(pp@pre, n@pre + 1, pp_values)
    */
    /*@ Inv Assert
          exists (pre_values : list Z) (pp_values : list Z)
                 (terms : list Z),
          s == s@pre && n == n@pre && term == term@pre &&
          pre == pre@pre && pp == pp@pre &&
          1 <= n@pre && n@pre <= 500000 &&
          n@pre == Zlength(text) &&
          (forall k, (0 <= k && k < n@pre) =>
             (65 <= text[k] && text[k] <= 90)) &&
          1 <= L && L <= n@pre + 1 && Zlength(terms) == L - 1 &&
          Zlength(pre_values) == n@pre + 1 &&
          Zlength(pp_values) == n@pre + 1 &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (0 <= pre_values[k] && pre_values[k] <= k)) &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (0 <= pp_values[k] && pp_values[k] <= k * (k + 1) / 2)) &&
          (forall k, (0 <= k && k < L - 1) =>
             (0 <= terms[k] && terms[k] <= n@pre * n@pre)) &&
          VowelPrefixCounts(text, pre_values) &&
          PrefixCountTotals(pre_values, pp_values) &&
          PrettyTermPrefix(text, terms) &&
          CharArray::full(s@pre, n@pre, text) *
          Int64Array::full(pre@pre, n@pre + 1, pre_values) *
          Int64Array::full(pp@pre, n@pre + 1, pp_values) *
          Int64Array::seg(term@pre, 0, L - 1, terms) *
          Int64Array::seg_shape(term@pre, L - 1, n@pre)
    */
    for (int L = 1; L <= n; L++) {
        /*@ Assert
              exists (pre_values : list Z) (pp_values : list Z)
                     (terms : list Z) (old_next : Z),
              s == s@pre && n == n@pre && term == term@pre &&
              pre == pre@pre && pp == pp@pre &&
              1 <= n@pre && n@pre <= 500000 &&
              n@pre == Zlength(text) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (65 <= text[k] && text[k] <= 90)) &&
              1 <= L && L <= n@pre && Zlength(terms) == L - 1 &&
              Zlength(pre_values) == n@pre + 1 &&
              Zlength(pp_values) == n@pre + 1 &&
              (forall k, (0 <= k && k < n@pre + 1) =>
                 (0 <= pre_values[k] && pre_values[k] <= k)) &&
              (forall k, (0 <= k && k < n@pre + 1) =>
                 (0 <= pp_values[k] &&
                  pp_values[k] <= k * (k + 1) / 2)) &&
              (forall k, (0 <= k && k < L - 1) =>
                 (0 <= terms[k] && terms[k] <= n@pre * n@pre)) &&
              VowelPrefixCounts(text, pre_values) &&
              PrefixCountTotals(pre_values, pp_values) &&
              PrettyTermPrefix(text, terms) &&
              CharArray::full(s@pre, n@pre, text) *
              Int64Array::full(pre@pre, n@pre + 1, pre_values) *
              Int64Array::full(pp@pre, n@pre + 1, pp_values) *
              Int64Array::seg(term@pre, 0, L - 1, terms) *
              data_at(term@pre + (L - 1) * sizeof(long long),
                      long long, old_next) *
              Int64Array::missing_i_shape(term@pre, L - 1, L - 1, n@pre)
        */
        long long hi = pp[n] - pp[L - 1]; /* sum of pre[L..n] */
        long long lo = pp[n - L];         /* sum of pre[0..n-L] */
        term[L - 1] = hi - lo;
    }
}

// int main(void)
// {
//     static char s[500005];
//     if (scanf("%500004s", s) != 1)
//         return 0;
//     int n = 0;
//     while (s[n])
//         n++;
//     static long long term[500005], pre[500006], pp[500006];
//     solver(s, n, term, pre, pp);
//     long double total = 0;
//     for (int L = 1; L <= n; L++)
//         total += (long double)term[L - 1] / L;
//     printf("%.7Lf\n", total);
//     return 0;
// }
