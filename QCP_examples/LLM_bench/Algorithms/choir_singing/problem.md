# P1091 Choir Formation

## Abstract model

Choose a subsequence of the students' heights that is strictly increasing up
to one peak and strictly decreasing afterward. If the longest such bitonic
subsequence has length $k$, the required number of removals is $n-k$. The
verification case computes increasing and decreasing DP lengths for every
possible peak.

## Problem statement

$n$ students stand in a fixed left-to-right order. Remove as few students as
possible so that the remaining heights have the form
$t_1<\cdots<t_i>\cdots>t_k$. The relative order of retained students may not
change. Output the minimum number removed.

## Input and output

The first line contains $n$ and the second line contains the $n$ heights.
Output the minimum removal count.

## Constraints

- $2 \le n \le 100$.
- $130 \le t_i \le 230$.
- For 50% of the original tests, $n \le 20$.

## Source

[Luogu P1091, NOIP 2004 Senior](https://www.luogu.com.cn/problem/P1091).
