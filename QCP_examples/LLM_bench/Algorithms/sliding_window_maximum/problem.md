# LeetCode 239: Sliding Window Maximum

## Abstract model

For each $i$ from $0$ through $n-k$, compute
$\max(nums_i,\ldots,nums_{i+k-1})$. The verification case keeps candidate
indices in a monotonically decreasing queue, giving linear total time, and
writes the $n-k+1$ maxima to a caller-provided output array.

## Problem statement

A window of length $k$ begins at the left end of `nums` and moves right one
position at a time. Return the maximum element visible at every position of
the window.

## Constraints

- $1 \le n \le 10^5$.
- $-10^4 \le nums_i \le 10^4$.
- $1 \le k \le n$.

## Source

[LeetCode 239, "Sliding Window Maximum"](https://leetcode.com/problems/sliding-window-maximum/).
