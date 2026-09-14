# P1063 Energy Necklace

## Abstract model

Represent the circular necklace by labels $a_1,\ldots,a_n$. Merging the two
subchains separated at $k$ inside interval $[i,j]$ releases
$a_i a_{k+1} a_{j+1}$. Duplicate the circle into a linear sequence and use
interval dynamic programming to maximize the accumulated energy over every
length-$n$ interval.

## Problem statement

Each bead has a head and tail label, and adjacent labels match. Merging beads
$(m,r)$ and $(r,n)$ releases $m r n$ energy and creates bead $(m,n)$. Repeatedly
merge adjacent beads until one remains. Choose the merge order that maximizes
total released energy.

## Input and output

The first line contains $N$. The second line contains the $N$ head labels in
clockwise order. Output the maximum total energy.

## Constraints

- $4 \le N \le 100$.
- Every label is a positive integer not exceeding $1000$.
- The answer does not exceed $2.1\times10^9$.

## Source

[Luogu P1063, NOIP 2006 Senior](https://www.luogu.com.cn/problem/P1063).
