# LeetCode 198: House Robber

## Abstract model

Choose a subset of array indices with no two consecutive indices and maximize
the sum of their nonnegative values. The verification case uses the rolling
recurrence `best(i) = max(best(i - 1), best(i - 2) + nums[i])`, keeping only
the previous two optimum values.

## Problem statement

Each element of `nums` is the money stored in one house along a street. Robbing
two adjacent houses triggers the alarm. Return the largest total amount that
can be taken without choosing adjacent houses.

## Constraints

- Original problem: $1 \le n \le 100$ and $0 \le nums_i \le 400$.
- Verification case: $0 \le n \le 10^5$ and $0 \le nums_i \le 10^4$.

## Source

[LeetCode 198, "House Robber"](https://leetcode.com/problems/house-robber/).
