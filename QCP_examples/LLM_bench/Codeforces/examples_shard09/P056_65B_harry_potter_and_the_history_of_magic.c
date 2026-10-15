/*
 * Codeforces 65/B - Harry Potter and the History of Magic  (rating 1700, GREEDY)
 *
 * Process the dates left to right keeping the smallest legal value: a smaller
 * current date never constrains later ones more.  For each date try every
 * one-digit edit (and no edit at all), keep those inside [1000, 2011] that are
 * at least the previous value, and take the minimum.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P056-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P056_65B_harry_potter_and_the_history_of_magic_lib */
/*@ Extern Coq
      (Spec : list Z -> option(list Z) -> Prop)
*/
/* QCP_INSERT_END:shard09-P056-solver-support */

/*@ Extern Coq
      (YearDigits : Z -> list Z)
      (DigitLower : Z -> Z)
      (CandidateValue : Z -> Z -> Z -> Z)
      (BestScanned : Z -> Z -> Z -> Z -> Z -> Prop)
      (NextYearResult : Z -> Z -> Z -> Prop)
      (GreedyPrefix : list Z -> list Z -> Prop)
      (PreviousYear : list Z -> Z)
*/

/* solver: pure.  Smallest value in [1000, 2011] that is >= prev and differs
 * from y in at most one digit, or -1 if there is none. */
static int next_year(int y, int prev)
/*@ Require
      1000 <= y && y <= 9999 && 1000 <= prev && prev <= 2011 && emp
    Ensure
      NextYearResult(y@pre, prev@pre, __return) && emp
*/
{
    int d[4] = {y / 1000, y / 100 % 10, y / 10 % 10, y % 10};
    int best = -1;
    /*@ Inv Assert
          y == y@pre && prev == prev@pre &&
          1000 <= y@pre && y@pre <= 9999 &&
          1000 <= prev@pre && prev@pre <= 2011 &&
          0 <= pos && pos <= 4 &&
          -1 <= best && best <= 2011 &&
          BestScanned(y@pre, prev@pre, pos, DigitLower(pos), best) &&
          0 <= YearDigits(y@pre)[0] && YearDigits(y@pre)[0] <= 9 &&
          0 <= YearDigits(y@pre)[1] && YearDigits(y@pre)[1] <= 9 &&
          0 <= YearDigits(y@pre)[2] && YearDigits(y@pre)[2] <= 9 &&
          0 <= YearDigits(y@pre)[3] && YearDigits(y@pre)[3] <= 9 &&
          IntArray::full(d, 4, YearDigits(y@pre))
    */
    for (int pos = 0; pos < 4; pos++) {
        int old = d[pos];
        /*@ Inv Assert
              exists (digits : list Z),
                y == y@pre && prev == prev@pre &&
                1000 <= y@pre && y@pre <= 9999 &&
                1000 <= prev@pre && prev@pre <= 2011 &&
                0 <= pos && pos < 4 &&
                old == YearDigits(y@pre)[pos] &&
                DigitLower(pos) <= v && v <= 10 &&
                -1 <= best && best <= 2011 &&
                BestScanned(y@pre, prev@pre, pos, v, best) &&
                ((v == DigitLower(pos) && digits == YearDigits(y@pre)) ||
                 (DigitLower(pos) < v &&
                  digits == replace_Znth(pos, v - 1, YearDigits(y@pre)))) &&
                0 <= digits[0] && digits[0] <= 9 &&
                0 <= digits[1] && digits[1] <= 9 &&
                0 <= digits[2] && digits[2] <= 9 &&
                0 <= digits[3] && digits[3] <= 9 &&
                IntArray::full(d, 4, digits)
        */
        for (int v = (pos == 0 ? 1 : 0); v <= 9; v++) {
            d[pos] = v;
            int cand = d[0] * 1000 + d[1] * 100 + d[2] * 10 + d[3];
            if (cand >= 1000 && cand <= 2011 && cand >= prev &&
                (best < 0 || cand < best))
                best = cand;
        }
        d[pos] = old;
    }
    return best;
}

/* solver: complete case.  Return 1 with the complete sequence, or 0 when the
 * frozen option-valued Spec requires None. */
static int solver(const int *years, int n, int *out)
/* QCP_INSERT_BEGIN:shard09-P056-normalized-solver-contract */
/*@ With (input_years : list Z)
    Require
      1 <= n && n <= 1000 && (forall i, (0 <= i && i < n) => (1000 <= input_years[i] && input_years[i] <= 9999)) && n == Zlength(input_years) && IntArray::full(years, n, input_years) * IntArray::full_shape(out, n)
    Ensure
      ((__return == 0 && Spec(input_years, None) && IntArray::full_shape(out, n)) || (exists (result : list Z), __return == 1 && Spec(input_years, Some(result)) && IntArray::full(out, n, result))) && IntArray::full(years, n, input_years)
*/
/* QCP_INSERT_END:shard09-P056-normalized-solver-contract */
{
    int prev = 1000;
    /*@ Inv Assert
          exists (done : list Z),
            years == years@pre && out == out@pre && n == n@pre &&
            1 <= n@pre && n@pre <= 1000 &&
            n@pre == Zlength(input_years) &&
            (forall k, (0 <= k && k < n@pre) =>
               (1000 <= input_years[k] && input_years[k] <= 9999)) &&
            0 <= i && i <= n@pre && i == Zlength(done) &&
            prev == PreviousYear(done) &&
            GreedyPrefix(input_years, done) &&
            IntArray::full(years@pre, n@pre, input_years) *
            IntArray::seg(out@pre, 0, i, done) *
            IntArray::seg_shape(out@pre, i, n@pre)
    */
    for (int i = 0; i < n; i++) {
        /*@ Assert
              exists (done : list Z) (old_out : Z),
                years == years@pre && out == out@pre && n == n@pre &&
                1 <= n@pre && n@pre <= 1000 &&
                n@pre == Zlength(input_years) &&
                (forall k, (0 <= k && k < n@pre) =>
                   (1000 <= input_years[k] && input_years[k] <= 9999)) &&
                0 <= i && i < n@pre && i == Zlength(done) &&
                prev == PreviousYear(done) &&
                GreedyPrefix(input_years, done) &&
                IntArray::full(years@pre, n@pre, input_years) *
                IntArray::seg(out@pre, 0, i, done) *
                data_at(out@pre + i * sizeof(int), int, old_out) *
                IntArray::missing_i_shape(out@pre, i, i, n@pre)
        */
        out[i] = next_year(years[i], prev);
        if (out[i] < 0)
            return 0;
        prev = out[i];
    }
    return 1;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int y[1005], z[1005];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &y[i]);
//     int ok = solver(y, n, z);
//     if (!ok) {
//         puts("No solution");
//         return 0;
//     }
//     for (int i = 0; i < n; i++)
//         printf("%d\n", z[i]);
//     return 0;
// }
