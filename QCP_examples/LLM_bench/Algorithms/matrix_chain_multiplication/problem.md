# Matrix-chain multiplication

## Abstract model

Matrix $A_i$ has dimensions $p_i\times p_{i+1}$. Every full parenthesization
computes the same product, but a split at $k$ inside $A_i\cdots A_j$ costs the
two subproblem optima plus $p_i p_{k+1}p_{j+1}$ scalar multiplications. Minimize
this cost over all full parenthesizations. The verification case fills an
interval-DP table declared inside the function.

## Problem statement

Given the compatible dimension sequence $p_0,p_1,\ldots,p_n$, determine the
minimum number of scalar multiplications needed to compute
$A_0A_1\cdots A_{n-1}$. The matrices themselves need not be multiplied.

For example, dimensions `30 35 15 5 10 20 25` describe six matrices and have
optimal cost `15125`.

## Constraints

The verification case uses $1\le n\le8$ and $1\le p_i\le100$. It declares
`cost[64]` locally and uses its first $n^2$ cells. These bounds keep every
cost at most $7,000,000$.

## Source

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
*Introduction to Algorithms*, 4th ed., MIT Press, 2022, Section 14.2
(Section 15.2 in the 3rd edition), "Matrix-chain multiplication."
