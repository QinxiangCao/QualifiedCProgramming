# P1899 Magic Items

## 题目描述

There are two types of items: ordinary items and magic items. Ordinary items have no magical properties, while magic items have some magical attributes. Each ordinary item has a single value $P$, but each magic item has two values: the value before identification $P_1$ and the value after identification $P_2$ (of course, $P_2$ is always greater than $P_1$).

To identify a magic item, you need to buy an identification scroll and use it on the magic item. After you identify one magic item, the scroll is consumed. Each identification scroll costs $P_i$ coins. If you do not have enough money, you cannot buy any identification scroll.

You are at a bazaar and currently hold many items. You know the value of each item and want to sell all of them. What is the maximum amount of money you can obtain?

You may assume:
- You start with no money.
- All magic items are initially unidentifed.
- As long as you have enough money, you may buy any number of identification scrolls.

## 输入格式

The first line contains two integers $N$ and $P_i$ ($1 \le P_i \le 5000$), denoting the number of items you own and the price of one identification scroll.  
The next $N$ lines each describe one item.  
For each ordinary item, the line contains a single integer $P$ ($1 \le P \le 10000$).  
For each magic item, the line contains two integers $P_1$ and $P_2$ ($1 \le P_1 < P_2 \le 10000$).

## 输出格式

Output a single integer: the maximum amount of money you can obtain.

## 输入输出样例 #1

### 输入 #1

```
2 10
10
20 100

```

### 输出 #1

```
100

```

## 说明/提示

For $30\%$ of the testdata, $1 \le N \le 50$.  
For $100\%$ of the testdata, $1 \le N \le 1000$.

Translated by ChatGPT 5