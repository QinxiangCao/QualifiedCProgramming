#define N 20
#define M 10
#define P 1000000007


#include "int_array_def.h"

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (PrefixDigitSum : Z -> Z -> Prop)
      (IntervalDigitSum : Z -> Z -> Z -> Prop)
      (PowerTable : list Z -> Prop)
      (PowerPrefix : list Z -> Z -> Prop)
      (DigitDPTable : list Z -> Prop)
      (DigitDPBaseProgress : list Z -> Z -> Prop)
      (DigitDPOuterProgress : list Z -> Z -> Prop)
      (DigitDPRowProgress : list Z -> Z -> Z -> Prop)
      (DigitDPCellProgress : list Z -> Z -> Z -> Z -> Prop)
      (ExtractedDigitBuffer : Z -> list Z -> Z -> Z -> Prop)
      (ExtractedDigitCount : Z -> Z -> Prop)
      (DigitPositionPower : Z -> Z -> Prop)
      (OuterDigitPositionPower : Z -> Z -> Prop)
      (InnerCandidateDigitProgress : list Z -> Z -> Z -> Z -> Z -> Prop)
      (AccumulatedDigitSumCorrect : Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_lib */

void digits_sum_init(int *dp, int *power)
/*@ Require
      IntArray::undef_full(dp, 200) *
      IntArray::undef_full(power, 20)
    Ensure
      exists dp_l power_l,
      DigitDPTable(dp_l) && PowerTable(power_l) &&
      IntArray::full(dp, 200, dp_l) *
      IntArray::full(power, 20, power_l)
 */
{
  power[0] = 1;
  /*@ Inv Assert
      exists power_l,
      dp == dp@pre && power == power@pre &&
      1 <= i && i <= 20 && Zlength(power_l) == i && PowerPrefix(power_l, i) &&
      IntArray::undef_full(dp@pre, 200) *
      IntArray::seg(power@pre, 0, i, power_l) *
      IntArray::undef_seg(power@pre, i, 20)
   */
  for (int i = 1; i < N; i++) {
    long long bef = power[i - 1];
    bef = bef * 10 % P;
    power[i] = (int)bef;
  }

  /*@ Inv Assert
      exists dp_l power_l,
      dp == dp@pre && power == power@pre &&
      0 <= i && i <= 20 && Zlength(dp_l) == i * 10 && Forall(eq(0), dp_l) &&
      PowerTable(power_l) &&
      IntArray::seg(dp@pre, 0, i * 10, dp_l) *
      IntArray::undef_seg(dp@pre, i * 10, 200) *
      IntArray::full(power@pre, 20, power_l)
   */
  for (int i = 0; i < N; i++) {
    /*@ Inv Assert
        exists dp_l power_l,
        dp == dp@pre && power == power@pre &&
        0 <= i && i < 20 && 0 <= j && j <= 10 &&
        Zlength(dp_l) == i * 10 + j && Forall(eq(0), dp_l) && PowerTable(power_l) &&
        IntArray::seg(dp@pre, 0, i * 10 + j, dp_l) *
        IntArray::undef_seg(dp@pre, i * 10 + j, 200) *
        IntArray::full(power@pre, 20, power_l)
     */
    for (int j = 0; j < M; j++) {
      dp[i * M + j] = 0;
    }
  }

  /*@ Inv Assert
      exists dp_l power_l,
      dp == dp@pre && power == power@pre &&
      0 <= j && j <= 10 && Zlength(dp_l) == 200 && DigitDPBaseProgress(dp_l, j) &&
      PowerTable(power_l) &&
      IntArray::full(dp@pre, 200, dp_l) *
      IntArray::full(power@pre, 20, power_l)
   */
  for (int j = 0; j < M; j++) {
    dp[M + j] = j;
  }

  /*@ Inv Assert
      exists dp_l power_l,
      dp == dp@pre && power == power@pre &&
      2 <= i && i <= 20 && Zlength(dp_l) == 200 && DigitDPOuterProgress(dp_l, i) &&
      PowerTable(power_l) &&
      IntArray::full(dp@pre, 200, dp_l) *
      IntArray::full(power@pre, 20, power_l)
   */
  for (int i = 2; i < N; i++) {
    /*@ Inv Assert
        exists dp_l power_l,
        dp == dp@pre && power == power@pre &&
        2 <= i && i < 20 && 0 <= j && j <= 10 &&
        Zlength(dp_l) == 200 && DigitDPRowProgress(dp_l, i, j) && PowerTable(power_l) &&
        IntArray::full(dp@pre, 200, dp_l) *
        IntArray::full(power@pre, 20, power_l)
     */
    for (int j = 0; j < M; j++) {
      /*@ Inv Assert
          exists dp_l power_l,
          dp == dp@pre && power == power@pre &&
          2 <= i && i < 20 && 0 <= j && j < 10 &&
          0 <= k && k <= 10 && Zlength(dp_l) == 200 && DigitDPCellProgress(dp_l, i, j, k) &&
          PowerTable(power_l) &&
          IntArray::full(dp@pre, 200, dp_l) *
          IntArray::full(power@pre, 20, power_l)
       */
      for (int k = 0; k < M; k++) {
        long long sub_power = power[i - 2];
        long long moving =
            (dp[(i - 1) * M + k] + sub_power * j % P) % P;
        long long new_dp = (dp[i * M + j] + moving) % P;
        dp[i * M + j] = (int)new_dp;
      }
    }
  }
}

int prefix_digits_sum(long long x, int *dp, int *digits)
/*@ With (dp_l : list Z)
    Require
      0 <= x && x <= 1000000000000000000 &&
      DigitDPTable(dp_l) &&
      IntArray::full(dp, 200, dp_l) *
      IntArray::undef_full(digits, 20)
    Ensure
      PrefixDigitSum(x, __return) &&
      IntArray::full(dp, 200, dp_l) *
      IntArray::undef_full(digits, 20)
 */
{
  int m = 0;
  int ans = 0;
  long long power_ll = 1;

  if (x < 1) {
    return 0;
  }

  /*@ Inv Assert
      exists digits_l,
      x == x@pre && dp == dp@pre && digits == digits@pre &&
      1 <= x@pre && x@pre <= 1000000000000000000 &&
      m == 0 && ans == 0 && power_ll == 1 &&
      0 <= i && i <= 20 && Zlength(digits_l) == i && Forall(eq(0), digits_l) &&
      DigitDPTable(dp_l) &&
      IntArray::full(dp@pre, 200, dp_l) *
      IntArray::seg(digits@pre, 0, i, digits_l) *
      IntArray::undef_seg(digits@pre, i, 20)
   */
  for (int i = 0; i < N; i++) {
    digits[i] = 0;
  }

  long long tmpx = x;
  /*@ Inv Assert
      exists digits_l,
      x == x@pre && dp == dp@pre && digits == digits@pre &&
      1 <= x@pre && x@pre <= 1000000000000000000 &&
      ans == 0 && power_ll == 1 &&
      0 <= m && m <= 19 && tmpx >= 0 &&
      (tmpx != 0 => m < 19) &&
      (tmpx == 0 => 1 <= m) &&
      (tmpx == 0 => ExtractedDigitCount(x@pre, m)) &&
      Zlength(digits_l) == 20 && ExtractedDigitBuffer(x@pre, digits_l, m, tmpx) &&
      DigitDPTable(dp_l) &&
      IntArray::full(dp@pre, 200, dp_l) *
      IntArray::full(digits@pre, 20, digits_l)
  */
  while (tmpx) {
    m = m + 1;
    digits[m] = (int)(tmpx % 10);
    tmpx /= 10;
  }

  /*@ Inv Assert
      exists digits_l,
      x == x@pre && dp == dp@pre && digits == digits@pre &&
      1 <= x@pre && x@pre <= 1000000000000000000 &&
      ans == 0 && tmpx == 0 &&
      1 <= i && i <= m && m <= 19 &&
      Zlength(digits_l) == 20 && ExtractedDigitBuffer(x@pre, digits_l, m, 0) &&
      ExtractedDigitCount(x@pre, m) && DigitPositionPower(i, power_ll) &&
      AccumulatedDigitSumCorrect(x@pre, m, ans) &&
      DigitDPTable(dp_l) &&
      IntArray::full(dp@pre, 200, dp_l) *
      IntArray::full(digits@pre, 20, digits_l)
   */
  for (int i = 1; i < m; i++) {
    power_ll *= 10;
  }

  /*@ Inv Assert
      exists digits_l,
      x == x@pre && dp == dp@pre && digits == digits@pre &&
      1 <= x@pre && x@pre <= 1000000000000000000 &&
      tmpx == 0 && 0 <= i && i <= m && m <= 19 &&
      0 <= ans && ans < 1000000007 &&
      Zlength(digits_l) == 20 && ExtractedDigitBuffer(x@pre, digits_l, m, 0) &&
      ExtractedDigitCount(x@pre, m) &&
      AccumulatedDigitSumCorrect(x@pre, i, ans) &&
      OuterDigitPositionPower(i, power_ll) && DigitDPTable(dp_l) &&
      IntArray::full(dp@pre, 200, dp_l) *
      IntArray::full(digits@pre, 20, digits_l)
   */
  for (int i = m; i > 0; i--) {
    /*@ Inv Assert
        exists digits_l answer_before,
        x == x@pre && dp == dp@pre && digits == digits@pre &&
        1 <= x@pre && x@pre <= 1000000000000000000 &&
        tmpx == 0 && 1 <= i && i <= m && m <= 19 &&
        0 <= digits_l[i] && digits_l[i] < 10 &&
        0 <= j && j <= digits_l[i] &&
        0 <= ans && ans < 1000000007 &&
        Zlength(digits_l) == 20 && ExtractedDigitBuffer(x@pre, digits_l, m, 0) &&
        ExtractedDigitCount(x@pre, m) &&
        InnerCandidateDigitProgress(dp_l, i, j, answer_before, ans) &&
        AccumulatedDigitSumCorrect(x@pre, i, answer_before) &&
        OuterDigitPositionPower(i, power_ll) && DigitDPTable(dp_l) &&
        IntArray::full(dp@pre, 200, dp_l) *
        IntArray::full(digits@pre, 20, digits_l)
     */
    for (int j = 0; j < digits[i]; j++) {
      ans = (ans + dp[i * M + j]) % P;
    }

    {
      long long current_digit = (x / power_ll) % 10;
      long long lower_digits = (x % power_ll + 1) % P;
      long long moving = lower_digits * current_digit % P;
      long long new_ans = (ans + moving) % P;
      ans = (int)new_ans;
    }

    power_ll /= 10;
  }

  return ans;
}

int interval_digits_sum(long long x, long long y)
/*@ Require
      1 <= x && x <= y && y <= 1000000000000000000 && emp
    Ensure
      IntervalDigitSum(x, y, __return) && emp
 */
{
  int dp[200];
  int power[20];
  int digits[20];
  /*@ Assert
      x == x@pre && y == y@pre &&
      1 <= x && x <= y && y <= 1000000000000000000 &&
      IntArray::undef_full(pointer_offset(dp, 0, sizeof(int), int), 200) *
      IntArray::undef_full(pointer_offset(power, 0, sizeof(int), int), 20) *
      IntArray::undef_full(pointer_offset(digits, 0, sizeof(int), int), 20)
   */
  digits_sum_init(dp, power);
  int ans1 = prefix_digits_sum(y, dp, digits);
  int ans2 = prefix_digits_sum(x - 1, dp, digits);
  /*@ Assert
      x == x@pre && y == y@pre &&
      1 <= x && x <= y && y <= 1000000000000000000 &&
      PrefixDigitSum(y, ans1) && PrefixDigitSum(x - 1, ans2) &&
      IntArray::undef_full(dp, 200) *
      IntArray::undef_full(power, 20) *
      IntArray::undef_full(digits, 20)
   */
  return ((ans1 - ans2) % P + P) % P;
}
