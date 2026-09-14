# P4999 Annoying Math Homework

## Abstract model

For an integer interval $[L,R]$, let $s(x)$ be the sum of the decimal digits
of $x$. Compute

$$
\left(\sum_{x=L}^{R}s(x)\right) \bmod (10^9+7).
$$

The verification case exposes initialization, prefix-sum, and interval-query
functions. It models an interval answer as the difference between two digit-DP
prefix answers.

## Problem statement

Mr. G gives $T$ queries. Each query contains two integers $L$ and $R$. For every
query, find the sum of the digit sums of all integers from $L$ through $R$,
inclusive, and report the result modulo $10^9+7$.

## Input and output

The first input line contains $T$. Each of the next $T$ lines contains $L$ and
$R$. Output one answer per query.

## Constraints

- $1 \le T \le 20$.
- $1 \le L \le R \le 10^{18}$.
- For 50% of the original tests, $R \le 10^8$.

## Source

[Luogu P4999, "Annoying Math Homework"](https://www.luogu.com.cn/problem/P4999?lang=en).
