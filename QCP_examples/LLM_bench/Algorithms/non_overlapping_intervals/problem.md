# LeetCode 435: Non-overlapping Intervals

## Abstract model

Choose a maximum-cardinality subset of half-open-compatible intervals: after
sorting by nondecreasing right endpoint, greedily retain each interval whose
left endpoint is at least the last retained right endpoint. The requested
removal count is the input size minus the maximum retained count. The C case
stores endpoints in parallel arrays and preserves each endpoint pair while
sorting.

## Problem statement

Given intervals $[start_i,end_i]$, remove as few as possible so that the
remaining intervals are pairwise non-overlapping. Intervals that only touch at
one endpoint, such as $[1,2]$ and $[2,3]$, do not overlap.

## Constraints

- Original problem: $1 \le n \le 10^5$.
- $-5\times10^4 \le start_i < end_i \le 5\times10^4$.
- Verification case: $0 \le n \le 1000$ and endpoints are in
  $[-10^4,10^4]$.

## Source

[LeetCode 435, "Non-overlapping Intervals"](https://leetcode.com/problems/non-overlapping-intervals/).
