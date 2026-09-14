# LeetCode 265: Paint House II

## Abstract model

Choose one of $k$ colors for each of $n$ houses, forbid equal colors on
adjacent houses, and minimize the sum of the chosen matrix entries. The
verification case evaluates the standard DP in $O(nk)$ time by retaining the
smallest and second-smallest costs of the previous row and a color attaining
the smallest value.

## Problem statement

There are $n$ houses in a row and $k$ colors. Painting house $i$ with color $c$
costs `costs[i][c]`. Paint every house so adjacent houses have different colors
and return the minimum total cost.

## Constraints

The verification case requires:

- $1 \le n \le 10^4$ and $2 \le k \le 1000$.
- $n k \le 10^6$.
- $0 \le costs[i][c] \le 10^4$.

## Source

[LeetCode 265, "Paint House II"](https://leetcode.com/problems/paint-house-ii/).
