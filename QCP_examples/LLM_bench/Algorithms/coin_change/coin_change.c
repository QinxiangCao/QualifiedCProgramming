



/*@ Extern Coq
      (ReachableAmount : list Z -> Z -> Prop)
      (MaxReachableAmount : list Z -> Z -> Z -> Prop)
      (DpPrefixZeroed : list Z -> Z -> Prop)
      (DpReachableTable : list Z -> list Z -> Z -> Prop)
      (DpCoinInnerProgress : list Z -> Z -> list Z -> Z -> Z -> Prop)
      (NoReachableAbove : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib */

int coinChange(int *coins, int coinsSize, int amount, int *dp)
/*@ With (coins_l : list Z)
    Require
      0 <= coinsSize && coinsSize <= 100000 &&
      0 <= amount && amount <= 100000 &&
      Zlength(coins_l) == coinsSize &&
      IntArray::full(coins, coinsSize, coins_l) *
      IntArray::undef_full(dp, amount + 1) &&
      (forall (k : Z), (0 <= k && k < coinsSize) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
    Ensure
      exists dp_l,
      MaxReachableAmount(coins_l, amount, __return) &&
      DpReachableTable(coins_l, dp_l, amount + 1) &&
      IntArray::full(coins, coinsSize, coins_l) *
      IntArray::full(dp, amount + 1, dp_l)
 */
{
  dp[0] = 1;
  /*@ Assert
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre && dp == dp@pre &&
      0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
      0 <= amount@pre && amount@pre <= 100000 &&
      Zlength(coins_l) == coinsSize@pre &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::seg(dp, 0, 1, cons(1, nil)) *
      IntArray::undef_seg(dp, 1, amount@pre + 1) &&
      (forall (k : Z), (0 <= k && k < coinsSize@pre) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
   */
  /*@ Inv Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre && dp == dp@pre &&
      0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
      0 <= amount@pre && amount@pre <= 100000 &&
      Zlength(coins_l) == coinsSize@pre &&
      1 <= j && j <= amount@pre + 1 &&
      DpPrefixZeroed(dp_l, j) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::seg(dp, 0, j, dp_l) *
      IntArray::undef_seg(dp, j, amount@pre + 1) &&
      (forall (k : Z), (0 <= k && k < coinsSize@pre) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
   */
  for (int j = 1; j <= amount; ++j) {
    dp[j] = 0;
  }

  /*@ Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre && dp == dp@pre &&
      0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
      0 <= amount@pre && amount@pre <= 100000 &&
      Zlength(coins_l) == coinsSize@pre &&
      DpPrefixZeroed(dp_l, amount@pre + 1) &&
      DpReachableTable(nil, dp_l, amount@pre + 1) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::full(dp, amount@pre + 1, dp_l) &&
      (forall (k : Z), (0 <= k && k < coinsSize@pre) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
   */
  /*@ Inv Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre && dp == dp@pre &&
      0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
      0 <= amount@pre && amount@pre <= 100000 &&
      Zlength(coins_l) == coinsSize@pre &&
      0 <= i && i <= coinsSize@pre &&
      DpReachableTable(sublist(0, i, coins_l), dp_l, amount@pre + 1) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::full(dp, amount@pre + 1, dp_l) &&
      (forall (k : Z), (0 <= k && k < coinsSize@pre) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
   */
  for (int i = 0; i < coinsSize; ++i) {
    int coin = coins[i];
    /*@ Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre && dp == dp@pre &&
      0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
      0 <= amount@pre && amount@pre <= 100000 &&
      Zlength(coins_l) == coinsSize@pre &&
      0 <= i && i < coinsSize@pre &&
      coin == coins_l[i] &&
      1 <= coin && coin <= INT_MAX &&
      DpReachableTable(sublist(0, i, coins_l), dp_l, amount@pre + 1) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::full(dp, amount@pre + 1, dp_l) &&
      (forall (k : Z), (0 <= k && k < coinsSize@pre) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
     */
    if (coin <= amount) {
      /*@ Inv Assert
        exists dp_l,
        coins == coins@pre && coinsSize == coinsSize@pre &&
        amount == amount@pre && dp == dp@pre &&
        0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
        0 <= amount@pre && amount@pre <= 100000 &&
        Zlength(coins_l) == coinsSize@pre &&
        0 <= i && i < coinsSize@pre &&
        coin == coins_l[i] &&
        1 <= coin && coin <= amount@pre &&
        coin <= j && j <= amount@pre + 1 &&
        DpCoinInnerProgress(sublist(0, i, coins_l), coin, dp_l, j, amount@pre) &&
        IntArray::full(coins, coinsSize@pre, coins_l) *
        IntArray::full(dp, amount@pre + 1, dp_l) &&
        (forall (k : Z), (0 <= k && k < coinsSize@pre) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
       */
      for (int j = coin; j <= amount; ++j) {
        if (dp[j - coin] != 0) {
          dp[j] = 1;
        }
      }
    }
    /*@ Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre && dp == dp@pre &&
      0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
      0 <= amount@pre && amount@pre <= 100000 &&
      Zlength(coins_l) == coinsSize@pre &&
      0 <= i && i < coinsSize@pre &&
      coin == coins_l[i] &&
      1 <= coin && coin <= INT_MAX &&
      DpReachableTable(sublist(0, i + 1, coins_l), dp_l, amount@pre + 1) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::full(dp, amount@pre + 1, dp_l) &&
      (forall (k : Z), (0 <= k && k < coinsSize@pre) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
     */
  }

  int res = amount;
  /*@ Inv Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre && dp == dp@pre &&
      0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
      0 <= amount@pre && amount@pre <= 100000 &&
      Zlength(coins_l) == coinsSize@pre &&
      0 <= res && res <= amount@pre &&
      DpReachableTable(coins_l, dp_l, amount@pre + 1) &&
      NoReachableAbove(coins_l, amount@pre, res) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::full(dp, amount@pre + 1, dp_l) &&
      (forall (k : Z), (0 <= k && k < coinsSize@pre) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
   */
  while (res > 0 && dp[res] == 0) {
    --res;
  }
  /*@ Assert
      exists dp_l,
      coins == coins@pre && coinsSize == coinsSize@pre &&
      amount == amount@pre && dp == dp@pre &&
      0 <= coinsSize@pre && coinsSize@pre <= 100000 &&
      0 <= amount@pre && amount@pre <= 100000 &&
      Zlength(coins_l) == coinsSize@pre &&
      0 <= res && res <= amount@pre &&
      DpReachableTable(coins_l, dp_l, amount@pre + 1) &&
      NoReachableAbove(coins_l, amount@pre, res) &&
      MaxReachableAmount(coins_l, amount@pre, res) &&
      IntArray::full(coins, coinsSize@pre, coins_l) *
      IntArray::full(dp, amount@pre + 1, dp_l)
   */
  return res;
}
