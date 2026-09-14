# P1311 Choosing Inns

## Abstract model

For every pair $i<j$, count it exactly when the two inns have the same color
and the minimum coffee-shop charge on the closed interval $[i,j]$ is at most
$p$. The verification case performs a left-to-right count using per-color
totals and per-color totals that have already passed an affordable shop.

## Problem statement

There are $n$ inns in order along a river. Inn $i$ has one of $k$ colors and a
coffee shop with minimum charge $b_i$. Two tourists choose different inns of
the same color. They can meet if at least one coffee shop between their inns,
including both endpoints, charges at most $p$. Output the number of valid
unordered choices.

## Input and output

The first line contains $n$, $k$, and $p$. Each of the next $n$ lines contains
an inn color $a_i$ and charge $b_i$. Output the number of valid pairs.

## Constraints

- $2 \le n \le 2\times10^5$ and $1 \le k \le 50$.
- $0 \le a_i < k$.
- $0 \le p \le 100$ and $0 \le b_i \le 100$.

## Source

[Luogu P1311, NOIP 2011 Senior](https://www.luogu.com.cn/problem/P1311).
