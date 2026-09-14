# LeetCode 5: Longest Palindromic Substring

## Abstract model

Among all contiguous substrings that read identically from left to right and
right to left, maximize the substring length. The verification case transforms
the input with separators, applies Manacher's linear-time radius algorithm,
and copies one maximum palindrome to a caller-provided output buffer.

## Problem statement

Given a string `s`, return a longest palindromic substring. If several longest
answers exist, any one may be returned.

## Constraints

- $1 \le |s| \le 1000$.
- `s` contains only digits and English letters.
- The verification output buffer has capacity $|s|+1$ including its terminator.

## Source

[LeetCode 5, "Longest Palindromic Substring"](https://leetcode.com/problems/longest-palindromic-substring/).
