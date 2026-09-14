# P2569 Stock Trading

## Abstract model

Use a DP state indexed by day and shares held. Transitions either keep the
previous holding or buy/sell within the daily limits from a state at least
$W+1$ days earlier. Holdings always stay in $[0,\mathrm{MaxP}]$. The objective
is maximum profit after day $T$.

## Problem statement

For each of the next $T$ days, the buy price, sell price, maximum purchasable
shares, and maximum sellable shares are known. Any two transaction days must
have at least $W$ complete days between them, and holdings may never exceed
`MaxP`. Starting with no shares and unlimited cash, maximize the profit earned
over the $T$ days.

## Input and output

The first line contains $T$, `MaxP`, and $W$. Each following line contains
$AP_i$, $BP_i$, $AS_i$, and $BS_i$. Output the maximum profit.

## Constraints

- $0 \le W < T \le 2000$ and $1 \le \mathrm{MaxP} \le 2000$.
- $1 \le BP_i \le AP_i \le 1000$.
- $1 \le AS_i,BS_i \le \mathrm{MaxP}$.
- The verification case uses reduced bounds $T,\mathrm{MaxP}\le990$.

## Source

[Luogu P2569, SCOI 2010](https://www.luogu.com.cn/problem/P2569?lang=en).
