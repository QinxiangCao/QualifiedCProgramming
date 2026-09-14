# Rod cutting

## Abstract model

For every integer rod length $j$, maximize total revenue over all compositions
of $j$ into positive piece lengths. The bottom-up recurrence considers the
first piece length $i$ and combines `price[i]` with the optimum for $j-i$. The
uncut rod is included by choosing $i=j$.

## Problem statement

A rod of integral length $n$ can be cut into integer-length pieces. The array
`price[i]` gives the selling price of one piece of length $i$. Determine the
greatest revenue obtainable by choosing any cuts, including no cut.

## Constraints

The verification case uses $0\le n\le1000$, `price[0] = 0`, and
$0\le price[i]\le10^6$. It fills `revenue[0..n]`, and its arithmetic
preconditions ensure that every optimum fits in a signed C `int`.

## Source

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
*Introduction to Algorithms*, 4th ed., MIT Press, 2022, Section 14.1
(Section 15.1 in the 3rd edition), "Rod cutting."
