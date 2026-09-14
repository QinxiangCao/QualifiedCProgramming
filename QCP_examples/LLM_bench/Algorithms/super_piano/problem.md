# P2048 Super Piano

## Abstract model

Every legal chord is an interval $[i,j]$ whose length lies in $[L,R]$, with
value equal to its subarray sum. Select $k$ distinct legal intervals with the
largest total value. The verification case uses prefix sums, range-maximum
queries, and a max-heap that lazily enumerates the $k$ largest interval sums.

## Problem statement

A piano has $n$ notes, and note $i$ has beauty $A_i$, which may be negative. A
super chord is a contiguous group of between $L$ and $R$ notes, and its beauty
is their sum. A composition contains $k$ distinct super chords. Output the
maximum possible sum of their beauties.

## Input and output

The first line contains $n$, $k$, $L$, and $R$. The next $n$ lines contain the
values $A_i$. Output the maximum composition beauty.

## Constraints

- Original problem: $1 \le n,k \le 5\times10^5$.
- $1 \le L \le R \le n$ and $-1000 \le A_i \le 1000$.
- At least $k$ legal intervals exist.
- Verification case: $n\le10^5$ and $n+k+1\le2\times10^5$.

## Source

[Luogu P2048, NOI 2010](https://www.luogu.com.cn/problem/P2048).
