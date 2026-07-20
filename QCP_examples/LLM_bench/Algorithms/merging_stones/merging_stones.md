# P1775 Merging Stones (Weakened Version)

## 题目描述

There are $N(N \le 300)$ piles of stones in a row, numbered $1, 2, 3, \cdots, N$. Each pile has a mass $m_i\ (m_i \le 1000)$. The goal is to merge these $N$ piles into one pile. Each time, you may only merge two adjacent piles, and the cost of merging is the sum of the masses of these two piles. After merging, the piles that were adjacent to the two merged piles become adjacent to the new pile. Because different merging orders lead to different total costs, find a method that minimizes the total cost, and output the minimum cost.

## 输入格式

The first line contains an integer $N$.
The second line contains $N$ integers $m_i$.

## 输出格式

Output a single integer, the minimum cost.

## 输入输出样例 #1

### 输入 #1

```
4
2 5 3 1
```

### 输出 #1

```
22
```
