# P11361 Edit Strings

## 题目描述

Xiao M has two binary strings $s_1$ and $s_2$ of length $n$ (character set $\{0, 1\}$).

Xiao M wants to maximize the number of positions where the corresponding characters in the two strings are the same, i.e., maximize the count of indices $i$ ($1 \leq i \leq n$) satisfying $s_{1,i} = s_{2,i}$. To achieve this, Xiao M has a string editing tool that allows swapping two **adjacent** characters in a string. However, some characters in the strings are marked as non-swappable. Xiao M can perform multiple swap operations on $s_1$ or $s_2$, and swappable characters can be moved any number of times.

Now, Xiao M wants to know the maximum number of matching positions that can be achieved after using the editing tool.

## 输入格式

**The problem contains multiple test cases.**

The first line of input contains an integer $T$, representing the number of test cases.

This is followed by $T$ test cases, each formatted as follows:

- The first line contains an integer $n$, the length of the strings.
- The second line contains a binary string $s_1$ of length $n$.
- The third line contains a binary string $s_2$ of length $n$.
- The fourth line contains a binary string $t_1$ of length $n$, where $t_{1,i} = 1$ means $s_{1,i}$ is swappable, and $t_{1,i} = 0$ means it is not.
- The fifth line contains a binary string $t_2$ of length $n$, where $t_{2,i} = 1$ means $s_{2,i}$ is swappable, and $t_{2,i} = 0$ means it is not.

## 输出格式

For each test case, output one line containing an integer, the maximum number of matching positions.

## 输入输出样例 #1

### 输入 #1

```
1
6
011101
111010
111010
101101
```

### 输出 #1

```
4
```

## 说明/提示

### Explanation for Sample #1

Initially, $s_1 = \tt{011101}$ (positions 4 and 6 are non-swappable), and $s_2 = \tt{111010}$ (positions 2 and 5 are non-swappable).

One possible sequence of operations:
1. Swap $s_{1,1}$ and $s_{1,2}$ to get $s_1 = \tt{101101}$.
2. Swap $s_{1,2}$ and $s_{1,3}$ to get $s_1 = \tt{110101}$.
3. Swap $s_{2,3}$ and $s_{2,4}$ to get $s_2 = \tt{110110}$.

Now, the first 4 positions of $s_1$ and $s_2$ match. It can be proven that no better solution exists, so the answer is 4.

### Explanation for Sample #2

See files `edit/edit2.in` and `edit/edit2.ans` in the attachment.

This sample contains 10 test cases, where the $i$-th test case ($1 \leq i \leq 10$) satisfies the constraints described for test point $2i - 1$ in the data range.

### Data Range

For all test data, it is guaranteed that: $1 \leq T \leq 10$, $1 \leq n \leq 10^5$.

| Test Case Number | $n \leq$ | Special Property |
| :--------------: | :------: | :--------------: |
|     1∼4          |   10     |       None       |
|     5,6          |  $10^3$  |        A         |
|     7,8          |  $10^5$  |        A         |
|     9,10         |  $10^3$  |        B         |
|     11,12        |  $10^5$  |        B         |
|     13,14        |  $10^3$  |        C         |
|     15,16        |  $10^5$  |        C         |
|     17,18        |  $10^3$  |       None       |
|     19,20        |  $10^5$  |       None       |

- **Special Property A**: All characters in $s_1$ are the same.
- **Special Property B**: $t_1 = t_2$.
- **Special Property C**: Exactly one '0' exists in each of $t_1$ and $t_2$.

Translated by DeepSeek R1