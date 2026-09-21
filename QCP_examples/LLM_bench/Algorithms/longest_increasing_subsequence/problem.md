# LeetCode 300: Longest Increasing Subsequence

## Abstract model

A subsequence retains the relative order of selected elements but need not be
contiguous. Among all subsequences whose values are strictly increasing,
maximize the number of selected elements. The verification case uses the
$O(n^2)$ DP in which `dp[i]` is the best length ending at index $i$.

## Problem statement

Given an integer array `nums`, return the length of its longest strictly
increasing subsequence.

## Constraints

- Original problem: $1 \le n \le 2500$ and $-10^4 \le nums_i \le 10^4$.
- Verification case: $1 \le n \le 10^5$.

The function declares `dp[100000]` locally and uses its first $n$ cells.
Its public inputs are `nums` and `numsSize`; the DP table is described only
by the internal annotations.

## Source

[LeetCode 300, "Longest Increasing Subsequence"](https://leetcode.com/problems/longest-increasing-subsequence/).
