# LeetCode 410: Split Array Largest Sum

## Abstract model

Partition a nonnegative array into exactly $k$ nonempty contiguous segments.
For each partition, take its largest segment sum; minimize that value over all
partitions. The verification case binary-searches the answer and greedily tests
whether a candidate bound needs at most $k$ segments.

## Problem statement

Given a nonnegative integer array `nums` and an integer $k$, split the array
into $k$ nonempty contiguous subarrays. Return the smallest possible value of
the largest subarray sum.

## Constraints

- Current source problem: $1 \le n \le 1000$, $0 \le nums_i \le 10^6$, and
  $1 \le k \le \min(50,n)$.
- Verification case: $1 \le n \le 10^5$, $1 \le k \le n$, and
  $0 \le nums_i < 10^8$, with total sum bounded by $10^9$.

## Source

[LeetCode 410, "Split Array Largest Sum"](https://leetcode.com/problems/split-array-largest-sum/).
