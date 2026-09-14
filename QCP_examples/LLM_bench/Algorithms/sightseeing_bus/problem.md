# P1315 [NOIP 2011 Senior] Sightseeing Bus

## 题目背景

Thanks to @Transhumanist for providing a set of hack testdata.

## 题目描述

In the scenic city Y, there are $n$ beautiful spots. As more tourists arrive, the city arranges a sightseeing bus to offer convenient transportation. The bus appears at spot $1$ at minute $0$, and then visits spots $2, 3, 4, \cdots, n$ in order. It takes $D_i$ minutes to go from spot $i$ to spot $i+1$. At any time, the bus can only move forward, or wait at a spot.

There are $m$ passengers in total. Each passenger needs exactly one ride from one spot to another. The $i$-th passenger arrives at spot $A_i$ at minute $T_i$ and wants to ride to spot $B_i$ ($A_i < B_i$). To ensure that all passengers can reach their destinations, the bus must, at each spot, wait until all passengers who need to depart from that spot have boarded, and then depart for the next spot.

Assume boarding and alighting take no time. A passenger’s travel time equals the time they reach their destination minus the time they arrive at their origin. Because there is only one bus and it sometimes needs to wait for other passengers, passengers complain that the travel time is too long. The clever driver ZZ installs $k$ nitro boosters. Each booster can decrease some $D_i$ by $1$. You may apply boosters multiple times to the same $D_i$, but must ensure that after all applications $D_i \ge 0$.

How should ZZ allocate the boosters to minimize the sum of all passengers’ travel times?

## 输入格式

- The first line contains $3$ integers $n, m, k$, separated by single spaces, denoting the number of spots, the number of passengers, and the number of boosters.
- The second line contains $n-1$ integers, separated by single spaces. The $i$-th integer is the travel time $D_i$ from spot $i$ to spot $i+1$.
- Lines $3$ to $m+2$: each line contains $3$ integers $T_i, A_i, B_i$, separated by single spaces. The $(i+2)$-th line gives the arrival time at the origin, the origin spot index, and the destination spot index for passenger $i$.

## 输出格式

Output a single integer: the minimal possible total travel time.

## 输入输出样例 #1

### 输入 #1

```
3 3 2
1 4
0 1 3
1 1 2
5 2 3
```

### 输出 #1

```
10

```

## 说明/提示

【Sample Explanation】

Use $2$ boosters on $D_2$, reducing the travel time from spot $2$ to spot $3$ to $2$ minutes.

The bus departs from spot $1$ at minute $1$, arrives at spot $2$ at minute $2$, departs from spot $2$ at minute $5$, and arrives at spot $3$ at minute $7$.

- Passenger $1$: travel time $=\,$ $7-0=7$ minutes.
- Passenger $2$: travel time $=\,$ $2-1=1$ minute.
- Passenger $3$: travel time $=\,$ $7-5=2$ minutes.

Total time $=\,$ $7+1+2=10$ minutes.

【Constraints】

- For $10\%$ of the testdata, $k=0$.
- For $20\%$ of the testdata, $k=1$.
- For $40\%$ of the testdata, $2 \le n \le 50$, $1 \le m \le 10^3$, $0 \le k \le 20$, $0 \le D_i \le 10$, $0 \le T_i \le 500$.
- For $60\%$ of the testdata, $1 \le n \le 100$, $1 \le m \le 10^3$, $0 \le k \le 100$, $0 \le D_i \le 100$, $0 \le T_i \le 10^4$.
- For $100\%$ of the testdata, $1 \le n \le 10^3$, $1 \le m \le 10^4$, $0 \le k \le 10^5$, $0 \le D_i \le 100$, $0 \le T_i \le 10^5$.