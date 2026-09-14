# P1368 Minimal Representation

## Abstract model

For a sequence $a_0,a_1,\ldots,a_{n-1}$, its cyclic rotation beginning at
position $p$ is

$$
(a_p,a_{p+1},\ldots,a_{n-1},a_0,a_1,\ldots,a_{p-1}).
$$

Compare two rotations lexicographically and choose the smallest one. If
several starting positions produce the same smallest rotation, choose the
smallest starting position. The C verification case uses a doubled sequence
and the linear-time two-candidate elimination algorithm.

## Problem statement

Given a circular sequence of $n$ integers, output its lexicographically
smallest cyclic rotation.

The verification function `minimal_representation` receives the sequence, a
working buffer, and an output array. It writes the smallest rotation into the
output array and returns the corresponding zero-based starting position in the
input sequence.

## Input and output

The original problem reads $n$ followed by $n$ integers and prints the
lexicographically smallest rotation, with adjacent values separated by spaces.

In the verification interface, `a` contains the $n$ input values, `b` is a
caller-provided working buffer with capacity for $2n$ values, and `out` has
capacity for $n$ values. The function copies the input twice into `b`. After
the function returns, `out` contains the smallest rotation and the return value
is an integer in $[0,n-1]$.

## Constraints

- Original problem: $1 \le n \le 300000$.
- Verification case: $1 \le n \le 1000$.
- Every sequence value is a signed C `int`.

## Source

[Luogu P1368, "Minimal Representation"](https://www.luogu.com.cn/problem/P1368).
