# P11361 Edit Strings

## Abstract model

Each binary string is divided into regions by characters that may not take part
in a swap. Within a connected swappable region, adjacent swaps allow arbitrary
permutations, so only the counts of zeroes and ones matter. Match fixed
characters and region inventories across the two strings to maximize equal
positions. The C case verifies this linear scan for one test instance.

## Problem statement

Two binary strings $s_1$ and $s_2$ have equal length $n$. Two mask strings
$t_1$ and $t_2$ mark whether each corresponding character may participate in
adjacent swaps. Any number of legal swaps may be performed in either string.
Find the maximum possible number of positions at which the final strings have
the same character.

## Input and output

The first line contains the number of test cases $T$. Each case contains $n$,
then $s_1$, $s_2$, $t_1$, and $t_2$. Output one maximum match count per case.

## Constraints

- $1 \le T \le 10$ and $1 \le n \le 10^5$.
- All four strings have length $n$ and contain only `0` and `1`.

## Source

[Luogu P11361, NOIP 2024](https://www.luogu.com.cn/problem/P11361).
