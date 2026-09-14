# P1044 Stack

## Abstract model

Start with the ordered input sequence $1,2,\ldots,n$, an empty stack, and an
empty output sequence. A legal execution repeatedly pushes the next input item
or pops the stack top. Count the distinct complete output sequences. This count
is the $n$-th Catalan number. The verification case computes the same count by
dynamic programming on the numbers of unprocessed inputs and stacked items; it
restricts $n$ to at most $7$.

## Problem statement

Stack A has capacity greater than $n$. Two operations are allowed: move the
first remaining operand to the stack top, or move the stack top to the end of
the output sequence. Given the initial operand sequence $1,2,\ldots,n$, output
the number of different output sequences obtainable after all operands have
been processed.

## Input and output

The input contains one integer $n$. Output the number of possible output
sequences.

## Constraints

- Original problem: $1 \le n \le 18$.
- Verification entry point: $0 \le n \le 7$.

## Source

[Luogu P1044, NOIP 2003 Junior, Problem 3](https://www.luogu.com.cn/problem/P1044).
