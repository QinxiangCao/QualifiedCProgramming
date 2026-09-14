# P1012 Concatenating Numbers

## Abstract model

Treat every positive integer as a decimal string and choose a permutation that
maximizes the concatenated string. This verification variant explores subsets
with dynamic programming rather than applying the usual $xy>yx$ comparison
sort; the mathematical objective is unchanged.

## Problem statement

Given $n$ positive integers, arrange all of them in one row and concatenate
adjacent decimal representations. Output the largest integer that can be
formed.

## Input and output

The first line contains $n$. The second line contains $n$ positive integers.
Output their maximum possible concatenation without separators.

## Constraints

- $1 \le n \le 20$.
- $1 \le a_i \le 10^9$.
- The verification workspace contains $2^n$ subset states.

## Source

[Luogu P1012, NOIP 1998 Senior, Problem 2](https://www.luogu.com.cn/problem/P1012).
