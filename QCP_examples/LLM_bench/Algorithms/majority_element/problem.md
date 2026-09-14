# LeetCode 169: Majority Element

## Abstract model

Find an element whose multiplicity is strictly greater than
$\lfloor n/2\rfloor$. Existence is guaranteed. The verification case implements
the Boyer-Moore cancellation process using one candidate and one vote counter.

## Problem statement

Given an integer array `nums` of length $n$, return its majority element. The
input is guaranteed to contain such an element.

## Constraints

- $1 \le n \le 5\times10^4$.
- $-10^9 \le nums_i \le 10^9$.
- A majority element always exists.

## Source

[LeetCode 169, "Majority Element"](https://leetcode.com/problems/majority-element/).
