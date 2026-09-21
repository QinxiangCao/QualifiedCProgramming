# Maximum Reachable Amount

This is a coin-change reachability variant. It is inspired by LeetCode 322,
but it does **not** solve the minimum-coin problem from that source.

## Abstract model

Let `coins` be a finite list of positive integer denominations. An amount $v$
is reachable if either:

- $v=0$; or
- there is a reachable amount $u$ and a denomination $c$ in `coins` such that
  $v=u+c$.

A denomination may be used any number of times. For a nonnegative upper bound
$A$, the required result is

$$
\max\{v \mid 0\le v\le A\text{ and }v\text{ is reachable}\}.
$$

The candidate set is never empty because $0$ is always reachable.

## Problem statement

Given zero or more positive coin denominations and a nonnegative target bound
`amount`, return the greatest reachable amount that does not exceed `amount`.
There is no requirement to reach `amount` exactly. If no positive amount at
most `amount` is reachable, return `0`.

Each denomination is reusable without limit. Duplicate denominations, if
present, do not change which amounts are reachable.

## C interface

```c
int coinChange(int *coins, int coinsSize, int amount);
```

- `coins[0..coinsSize)` contains the positive denominations and is preserved.
- The function declares the initially uninitialized array `dp[100001]`
  locally and uses its first `amount + 1` cells.
- The return value is the maximum reachable amount in the closed interval
  $[0,\texttt{amount}]$.

## Internal workspace semantics

Before returning, the internal `dp` table describes reachability for every
value from `0` through `amount`:

```text
dp[v] == 1  if and only if v is reachable from the denominations
dp[v] == 0  otherwise
```

This table property belongs to the function's internal annotations. The
local array's lifetime ends when the function returns.

The implementation initializes only `0` as reachable. It then processes each
denomination and scans amounts in increasing order. This forward scan permits
the current denomination to be reused any number of times. Finally, it scans
downward from `amount` and returns the first reachable value.

## Constraints

- $0 \le \texttt{coinsSize} \le 100000$.
- $0 \le \texttt{amount} \le 100000$.
- $1 \le \texttt{coins[i]} \le \texttt{INT\_MAX}$ for every valid index.
- `coins` contains exactly `coinsSize` integers.

The implementation runs in $O(\texttt{coinsSize}\times\texttt{amount})$ time.
The verification implementation reserves 100001 local integers and uses
the first `amount + 1` cells as its reachability table.

## Examples

```text
coins = [1, 2, 5], amount = 11  ->  11
coins = [2],       amount = 3   ->  2
coins = [4, 6],    amount = 7   ->  6
coins = [],        amount = 10  ->  0
coins = [3],       amount = 0   ->  0
```

## Difference from LeetCode 322

LeetCode 322 asks for the minimum number of coins needed to form `amount`
exactly and requires `-1` when exact formation is impossible. This verification
case stores only Boolean reachability, does not count coins, returns the
largest reachable value at most `amount`, and always returns a value in
$[0,\texttt{amount}]$.

## Source

Adapted as a reachability variant from
[LeetCode 322, "Coin Change"](https://leetcode.com/problems/coin-change/).
