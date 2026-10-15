/* Codeforces 1454/D - Number into Sequence */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P033_1454D_number_into_sequence.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Prop)
      (Int64Array::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P033_1454D_number_into_sequence_lib */
/*@ Extern Coq
      (FactorSearchState : Z -> Z -> Z -> Z -> Z -> Prop)
      (FactorExtractState : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (BestPowerChoice : Z -> Z -> Z -> Prop)
      (OutputPrefixState : Z -> Z -> Z -> Z -> Z -> list Z -> Prop)
      (FinalOutputSequence : Z -> Z -> Z -> Z -> list Z -> Prop)
      (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
*/
/*@ Extern Coq
      (FactorSearchProfile : Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (FactorExtractProfile : Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (FactorExtractOrigin : Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (FactorExtractGuard : Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P033_1454D_number_into_sequence.support */
static int solver(long long n,
                  long long *out) /* QCP_INSERT_BEGIN:P033_1454D_number_into_sequence.contract */

/*@
    Require
      2 <= n && n <= 10000000000 &&
      Int64Array::undef_full(out, 64)
    Ensure
      exists result,
        Spec(n, result) && __return == Zlength(result) &&
        Int64Array::full(out, __return, result) *
        Int64Array::undef_seg(out, __return, 64)
*/
/* QCP_INSERT_END:P033_1454D_number_into_sequence.contract */

{
    long long value = n, best_prime = n;
    int best_exp = 1;
    /*@ Inv Assert
          exists (ps : list Z) (es : list Z),
          n == n@pre && out == out@pre &&
          2 <= n@pre && n@pre <= 10000000000 &&
          1 <= value && value <= n@pre &&
          2 <= p && p <= 100001 &&
          p * p <= 1000000000000000000 &&
          1 <= best_exp && best_exp <= 64 &&
          2 <= best_prime && best_prime <= n@pre &&
          FactorSearchState(n@pre, value, p, best_prime, best_exp) &&
          FactorSearchProfile(n@pre, value, p, best_prime, best_exp, ps, es) &&
          Int64Array::undef_full(out, 64)
     */
    for (long long p = 2; p * p <= value; ++p)
        if (value % p == 0)
        {
            int e = 0;
            /*@ Inv Assert
              exists (ps : list Z) (es : list Z),
              n == n@pre && out == out@pre &&
              2 <= n@pre && n@pre <= 10000000000 &&
              1 <= value && value <= n@pre &&
              2 <= p && p <= 100001 &&
              0 <= e && e <= 64 &&
              1 <= best_exp && best_exp <= 64 &&
              2 <= best_prime && best_prime <= n@pre &&
              (e == 0 => value % p == 0) &&
              FactorExtractGuard(value, p, e) &&
              FactorExtractState(n@pre, value, p, e, best_prime, best_exp) &&
              FactorExtractOrigin(n@pre, value, p, e, best_prime, best_exp, ps, es) &&
              Int64Array::undef_full(out, 64)
         */
            while (value % p == 0)
            {
                value /= p;
                ++e;
            }
            /*@ Assert
              exists (ps : list Z) (es : list Z),
              n == n@pre && out == out@pre &&
              2 <= n@pre && n@pre <= 10000000000 &&
              1 <= value && value <= n@pre &&
              2 <= p && p <= 100001 &&
              1 <= e && e <= 64 &&
              1 <= best_exp && best_exp <= 64 &&
              2 <= best_prime && best_prime <= n@pre &&
              value % p != 0 &&
              FactorExtractGuard(value, p, e) &&
              FactorExtractState(n@pre, value, p, e, best_prime, best_exp) &&
              FactorExtractOrigin(n@pre, value, p, e, best_prime, best_exp, ps, es) &&
              FactorExtractProfile(n@pre, value, p, e, best_prime, best_exp, ps, es) &&
              Int64Array::undef_full(out, 64)
         */
            if (e > best_exp)
            {
                best_exp = e;
                best_prime = p;
            }
        }
    /*@ Assert
          n == n@pre && out == out@pre &&
          2 <= n@pre && n@pre <= 10000000000 &&
          1 <= value && value <= n@pre &&
          1 <= best_exp && best_exp <= 64 &&
          2 <= best_prime && best_prime <= n@pre &&
          BestPowerChoice(n@pre, best_prime, best_exp) &&
          Int64Array::undef_full(out, 64)
     */
    long long rest = n;
    /*@ Inv Assert
          exists (written : list Z),
          n == n@pre && out == out@pre &&
          2 <= n@pre && n@pre <= 10000000000 &&
          1 <= value && value <= n@pre &&
          1 <= best_exp && best_exp <= 64 &&
          2 <= best_prime && best_prime <= n@pre &&
          0 <= i && i < best_exp &&
          1 <= rest && rest <= n@pre &&
          BestPowerChoice(n@pre, best_prime, best_exp) &&
          OutputPrefixState(n@pre, best_prime, best_exp, i, rest, written) &&
          Int64Array::seg(out, 0, i, written) *
          Int64Array::undef_seg(out, i, 64)
     */
    for (int i = 0; i + 1 < best_exp; ++i)
    {
        out[i] = best_prime;
        rest /= best_prime;
    }
    /*@ Assert
          exists (written : list Z),
          n == n@pre && out == out@pre &&
          2 <= n@pre && n@pre <= 10000000000 &&
          1 <= value && value <= n@pre &&
          1 <= best_exp && best_exp <= 64 &&
          2 <= best_prime && best_prime <= n@pre &&
          1 <= rest && rest <= n@pre &&
          BestPowerChoice(n@pre, best_prime, best_exp) &&
          OutputPrefixState(n@pre, best_prime, best_exp, best_exp - 1, rest, written) &&
          Int64Array::seg(out, 0, best_exp - 1, written) *
          Int64Array::undef_seg(out, best_exp - 1, 64)
     */
    out[best_exp - 1] = rest;
    /*@ Assert
          exists (result : list Z),
          n == n@pre && out == out@pre &&
          2 <= n@pre && n@pre <= 10000000000 &&
          1 <= value && value <= n@pre &&
          1 <= best_exp && best_exp <= 64 &&
          FinalOutputSequence(n@pre, best_prime, best_exp, rest, result) &&
          Spec(n@pre, result) &&
          Int64Array::full(out, best_exp, result) *
          Int64Array::undef_seg(out, best_exp, 64)
     */
    return best_exp;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         long long n, out[64]; scanf("%lld", &n);
//         int count = solver(n, out); printf("%d\n", count);
//         for (int i = 0; i < count; ++i) printf("%lld%c", out[i], i + 1 == count ? '\n' : ' ');
//     }
//     return 0;
// }
