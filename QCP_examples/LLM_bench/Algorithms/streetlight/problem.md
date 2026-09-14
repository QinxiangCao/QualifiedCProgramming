# P1220 Turning Off Streetlights

## Abstract model

After the starting light is switched off, the set of extinguished lights in
an optimal walk can be represented as an interval containing the start. A DP
state stores the minimum consumed energy for an extinguished interval and for
the walker being at its left or right endpoint. Extending the interval adds
travel time multiplied by the total power of all lights still on.

## Problem statement

$n$ streetlights lie on a road in increasing position order. Each has a power
rating. A worker begins at light $c$, immediately turns it off, and then walks
at one metre per second to turn off the others. Switching time is negligible.
Minimize the energy consumed by all lights from the start until every light is
off.

## Input and output

The first line contains $n$ and $c$. Each of the next $n$ lines contains a
position and power. Output the minimum energy in joules.

## Constraints

- $1 \le n \le 50$ and $1 \le c \le n$.
- Positions are strictly increasing; the original positions are in $[1,100]$.
- $1 \le W_i \le 100$.

## Source

[Luogu P1220, "Turning Off Streetlights"](https://www.luogu.com.cn/problem/P1220).
