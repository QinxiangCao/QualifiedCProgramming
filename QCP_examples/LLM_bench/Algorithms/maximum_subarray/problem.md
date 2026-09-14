# LeetCode 53: Maximum Subarray

## Abstract model

Maximize $\sum_{i=l}^{r}nums_i$ over every nonempty contiguous interval
$0\le l\le r<n$. The verification case uses Kadane's recurrence, storing the
best suffix ending at the current element and the best interval seen so far.

## Problem statement

Given an integer array `nums`, return the sum of the contiguous nonempty
subarray with the largest sum.

## Constraints

- $1 \le n \le 10^5$.
- $-10^4 \le nums_i \le 10^4$.

## Source

[LeetCode 53, "Maximum Subarray"](https://leetcode.com/problems/maximum-subarray/).
