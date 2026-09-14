# LeetCode 11: Container With Most Water

## Abstract model

For every pair of indices $0 \le i < j < n$, the corresponding container has
area

$$
(j-i)\min(height_i,height_j).
$$

Return the maximum of these areas. The input array is read-only.

## Problem statement

An array `height` describes vertical lines at integer x-coordinates: line $i$
extends from $(i,0)$ to $(i,height_i)$. Choose two lines which, together with
the x-axis, form a non-slanted container holding as much water as possible,
and return that maximum amount.

## Verification case

`container_with_most_water_nlogn.c` sorts `(height, original index)` pairs in
descending height order. While scanning the sorted pairs, it tracks the minimum
and maximum original indices already processed, so the current bar can be
paired with its farthest eligible endpoint. The implementation runs in
$O(n\log n)$ time and uses four caller-provided work arrays, through which it
also returns the sorted height/index workspace.

## Constraints

- $n = \operatorname{length}(height)$.
- $2 \le n \le 10^5$.
- $0 \le height_i \le 10^4$.

Under these bounds the maximum possible area is
$(10^5-1)\times10^4=999{,}990{,}000$, which fits in a 32-bit signed integer.

## Source

[LeetCode 11, "Container With Most Water"](https://leetcode.com/problems/container-with-most-water/).
