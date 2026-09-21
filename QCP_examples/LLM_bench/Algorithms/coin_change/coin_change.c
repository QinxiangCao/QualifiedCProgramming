/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (MaxReachableAmount : list Z -> Z -> Z -> Prop)
      (DpPrefixZeroed : list Z -> Z -> Prop)
      (DpReachableTable : list Z -> list Z -> Z -> Prop)
      (DpCoinInnerProgress : list Z -> Z -> list Z -> Z -> Z -> Prop)
      (NoReachableAbove : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib */

int coinChange(int *coins, int coinsSize, int amount)
/*@ With (coins_l : list Z)
    Require
      0 <= coinsSize && coinsSize <= 100000 &&
      0 <= amount && amount <= 100000 &&
      Forall(Z::le(1), coins_l) && Forall(Z::ge(INT_MAX), coins_l) &&
      IntArray::full(coins, coinsSize, coins_l)
    Ensure
      MaxReachableAmount(coins_l, amount, __return) &&
      IntArray::full(coins, coinsSize, coins_l)
 */
{
  int dp[100001];

  dp[0] = 1;
  /*@ Inv Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre &&
      0 <= coinsSize && coinsSize <= 100000 &&
      amount <= 100000 && 1 <= j && j <= amount + 1 &&
      Forall(Z::le(1), coins_l) &&
      DpPrefixZeroed(dp_l, j) &&
      IntArray::full(coins, coinsSize, coins_l) *
      IntArray::seg(dp, 0, j, dp_l) *
      IntArray::undef_seg(dp, j, amount + 1) *
      IntArray::undef_seg(dp, amount + 1, 100001)
   */
  for (int j = 1; j <= amount; ++j) {
    dp[j] = 0;
  }

  /*@ Inv Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre &&
      coinsSize <= 100000 && 0 <= amount && amount <= 100000 &&
      0 <= i && i <= coinsSize &&
      Forall(Z::le(1), coins_l) &&
      DpReachableTable(sublist(0, i, coins_l), dp_l, amount + 1) &&
      IntArray::full(coins, coinsSize, coins_l) *
      IntArray::full(dp, amount + 1, dp_l) *
      IntArray::undef_seg(dp, amount + 1, 100001)
   */
  for (int i = 0; i < coinsSize; ++i) {
    int coin = coins[i];
    if (coin <= amount) {
      /*@ Inv Assert
        exists dp_l,
        coins == coins@pre && coinsSize == coinsSize@pre &&
        amount == amount@pre &&
        coinsSize <= 100000 && amount <= 100000 &&
        0 <= i && i < coinsSize &&
        Forall(Z::le(1), coins_l) &&
        coin == coins_l[i] && 1 <= coin && coin <= amount &&
        coin <= j && j <= amount + 1 &&
        DpCoinInnerProgress(sublist(0, i, coins_l), coin, dp_l, j, amount) &&
        IntArray::full(coins, coinsSize, coins_l) *
        IntArray::full(dp, amount + 1, dp_l) *
      IntArray::undef_seg(dp, amount + 1, 100001)
       */
      for (int j = coin; j <= amount; ++j) {
        if (dp[j - coin] != 0) {
          dp[j] = 1;
        }
      }
    }
  }

  int res = amount;
  /*@ Inv Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre &&
      0 <= res && res <= amount &&
      DpReachableTable(coins_l, dp_l, amount + 1) &&
      NoReachableAbove(coins_l, amount, res) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::full(dp, amount + 1, dp_l) *
      IntArray::undef_seg(dp, amount + 1, 100001)
   */
  while (res > 0 && dp[res] == 0) {
    --res;
  }
  /*@ Assert
      coins == coins@pre && amount == amount@pre && coinsSize == coinsSize@pre &&
      MaxReachableAmount(coins_l, amount@pre, res) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::undef_full(dp, 100001)
   */
  return res;
}
