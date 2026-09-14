# P1080 The King's Game

## Abstract model

The king is fixed first. For a minister at position $i$, the reward is the
floor of the product of all preceding left-hand values divided by that
minister's right-hand value. Find a permutation minimizing the maximum reward.
The verification case returns an optimal minister order and uses reduced
bounds ($n\le8$ and hand values at most $10$) so all arithmetic fits in C
integers.

## Problem statement

The king and each of $n$ ministers write one positive integer on each hand.
The king stands first and the ministers are arranged behind him. Each minister
receives the product of all left-hand numbers before that minister, divided by
the minister's own right-hand number and rounded down. Reorder the ministers so
that the largest reward received by any minister is as small as possible.

## Input and output

The input gives $n$, the king's two numbers, and then the two numbers for each
minister. The original problem outputs the minimized maximum reward; this
verification case materializes an order attaining that optimum.

## Constraints

- Original problem: $1 \le n \le 1000$ and $0<a,b<10000$.
- Verification case: $1 \le n \le 8$ and $1\le a,b\le10$.

## Source

[Luogu P1080, NOIP 2012 Senior](https://www.luogu.com.cn/problem/P1080).
