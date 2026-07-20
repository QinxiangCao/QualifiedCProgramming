# Correct Example: Binary Answer Annotation

本文件是 annotation 正例解析。遇到“二分答案 + check 判定函数”时，先学习这里的 spec 拆分和 invariant 形状，再写当前 case 的 `formal_case_lib` 和 C annotation。

## Example Files

本目录中的相关文件：

- `binary-search-annotation.md`：二分答案正例解析，说明 `CanX` / `CannotX` / `OptimalX` 的设计方式。
- `split_array_largest_sum/binary-search-annotation.md`：完整教学说明，展示最大段和最小值问题如何拆分 spec、判定函数和二分 invariant。
- `split_array_largest_sum/split_array_largest_sum.c`：配套 C annotation 示例，用于观察 `Require`、`Ensure`、`Inv Assert` 和 `where` 的组织方式。

学习这些例子时，只复用 spec 拆分、predicate-first annotation、array predicate 选型和 loop invariant 形状；不要把 proof script、generated artifact 或其他 case 的 formal 文件机械复制到当前 case。

## 适用模式

程序通常有两个层次：

- `check(arr, n, cap, ...)` 顺序扫描输入，判断候选答案 `cap` 是否可行。
- 主函数对答案空间做二分，根据 `check(mid)` 缩小 `[left, right]`，最后返回最小可行答案。

这类 case 的 annotation 核心不是复述二分循环，而是分离三类数学事实：

- `check` 的前缀扫描状态。
- 候选值是否可行的全局性质。
- 真实数学答案与当前二分边界的夹逼关系。

## Recommended Spec Shape

在 `formal_case_lib` 中定义业务语义 wrapper，而不是在 C annotation 中展开 `MaxMinLib`：

```coq
Definition CanSplit (l : list Z) (m cap : Z) : Prop := ...
Definition CannotSplit (l : list Z) (m cap : Z) : Prop := ...
Definition MinimizedMaxSegmentSum (l : list Z) (m ans : Z) : Prop := ...
```

若要表达“所有合法方案中的最大值最小”，优先在这些 wrapper 内使用 `MaxMinLib` 的 `min_value_of_subset` / `max_value_of_subset`。C annotation 只声明并调用 wrapper：

```c
/*@ Extern Coq
      (CanSplit : list Z -> Z -> Z -> Prop)
      (CannotSplit : list Z -> Z -> Z -> Prop)
      (MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop)
 */
```

## `check` Function

`check` 的 `Ensure` 只暴露判定性质：

```c
Ensure
  (__return == 1 => CanSplit(l, m, cap)) &&
  (__return == 0 => CannotSplit(l, m, cap)) &&
  IntArray::full(arr, n, l)
```

内部循环用一个前缀状态连接局部变量和数学含义：

```c
Inv Assert
  0 <= i && i <= n@pre &&
  1 <= cnt && cnt <= i + 1 &&
  0 <= cur && cur <= cap@pre &&
  PrefixSplitState(l, cap@pre, i, cnt, cur) &&
  IntArray::full(arr, n@pre, l)
```

`PrefixSplitState` 描述“扫描到前缀 `i` 时已经形成的段满足 cap 约束”，不是一份 Rocq 版 `check` 程序。

## Main Loop

主循环 invariant 维护真实答案被当前边界夹住：

```c
Inv Assert
  exists ans,
    arr == arr@pre && n == n@pre && m == m@pre &&
    Zlength(l) == n@pre &&
    IntArray::full(arr, n@pre, l) &&
    0 <= left && left <= right && right <= 1000000000 &&
    left <= ans && ans <= right &&
    MinimizedMaxSegmentSum(l, m, ans)
```

这里 `ans` 是数学答案，不是程序变量。循环保持只需证明：

- `CanSplit(l, m, mid)` 推出 `ans <= mid`，所以可令 `right = mid`。
- `CannotSplit(l, m, mid)` 推出 `mid < ans`，所以可令 `left = mid + 1`。

这些连接事实应在 proof side 作为 helper lemma 证明；annotation 只保留调用 helper 所需的前提。

## Checklist

- `check` 的返回值是否封装成 `CanX` / `CannotX` 判定性质？
- 主问题是否用 `Minimized...`、`Maximized...` 或等价数学 wrapper 表达？
- 主循环 invariant 是否包含真实答案在 `[left, right]` 内？
- `ok` 分支是否保留了可行 / 不可行事实、`mid` 范围和边界事实？
- C annotation 是否描述数学状态，而不是追踪一份 Rocq 版二分程序？

## How To Use The Example

遇到二分答案、可行性判定、最大最小值优化或 `check` helper 函数时：

1. 先读本文件，确定当前 case 是否属于同一算法形态。
2. 再读 `split_array_largest_sum/binary-search-annotation.md`，学习如何把 `check` 的前缀状态、候选可行性和真实答案边界分离。
3. 最后查看 `split_array_largest_sum/split_array_largest_sum.c` 中的 C annotation，重点观察函数 spec、主循环 invariant、`check` invariant 和函数调用处如何保留纯事实。

核心判断标准：

- spec 先用 `formal_case_lib` wrapper 描述数学语义。
- `check` 函数只对外暴露可行 / 不可行判定。
- 主循环 invariant 维护真实答案落在当前 `[left, right]` 内。
- proof-side bridge lemma 不塞进 C annotation；由 group-worker 证明当前 group suffix helper，或在 annotation round 中把必要数学定义提升为 seed declaration。
