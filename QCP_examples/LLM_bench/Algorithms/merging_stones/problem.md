# P1775 Merging Stones (Simplified Version)

## Abstract model

For every interval $[i,j]$, minimize the cost of merging it into one pile. A
split after $k$ contributes the optimal costs of $[i,k]$ and $[k+1,j]$ plus
the total mass in $[i,j]$. Prefix sums and interval DP evaluate all splits.

## Problem statement

$N$ stone piles are arranged in a line. One operation merges two adjacent
piles and costs their combined mass. Continue until one pile remains. Output
the minimum possible total cost over all merge orders.

## Input and output

The first line contains $N$ and the second contains the pile masses $m_i$.
Output the minimum total merge cost.

## Constraints

- Original problem: $1 \le N \le 300$ and $m_i \le 1000$.
- Verification case: $1 \le N \le 8$.

## Source

[Luogu P1775, "Merging Stones (Simplified Version)"](https://www.luogu.com.cn/problem/P1775).
