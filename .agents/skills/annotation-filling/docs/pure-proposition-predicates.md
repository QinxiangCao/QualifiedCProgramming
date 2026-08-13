# Annotation 中的纯命题谓词

本指南只用于 annotation 阶段：如何在 C annotation 与 case-level spec 中选择和书写已有的纯命题谓词。Rocq 证明侧的展开、桥接、改写和 helper lemma 属于 `group-worker-proving`。

核心规则：书写程序必须维持的数学事实。优先使用已有语义谓词，不要只为方便证明而暴露面向证明的结构，也不要在 `formal_case_lib` 中重复定义已有谓词。

## 在 C Annotation 中导入名称

C annotation 直接提及 Rocq 纯谓词时，在 C 文件顶部声明该名称：

```c
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (strict_lowerbound : Z -> list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sortArray_lib */
```

遵循以下规则：

- 在 `Extern Coq` 中列出 annotation 正文出现的名称。
- import 使这些名称可用于 generated Rocq 文件的 case lib 或 shared lib。
- 如果谓词来自当前 `formal_case_lib`，在 annotation 中按名称调用；不要把定义体复制进 C annotation。
- 如果已有 lib 提供相同语义，就使用已有名称。不要新增 `increasing_aux`、`NondecreasingZList` 或 `StrictlyIncreasingZList` 等重复名称。

## 函数 Spec

函数 spec 应陈述所需的输入/输出数学事实：

```c
/*@ With (l : list Z)
    Require
      Zlength(l) == numsSize &&
      1 <= numsSize && numsSize <= 50000 &&
      IntArray::full(nums, numsSize, l)
    Ensure
      exists l1,
      Permutation(l, l1) &&
      increasing(l1) &&
      Zlength(l1) == numsSize &&
      IntArray::full(__return, numsSize, l1)
 */
```

选择规则：

- 排序结果：写 `Permutation(l, l1) && increasing(l1)`；结果降序时写 `decreasing(l1)`。
- 求和结果：写 `__return == sum(l)`；在循环中维持 `ret == sum(sublist(0, i, l))` 等事实。
- 最大值、最小值或最优值：在 `formal_case_lib` 中定义清晰的数学谓词，例如 `MinimizedMaxSegmentSum(l, m, ans)`，再从 `Require` / `Ensure` 调用它。
- 仍要显式陈述长度、元素范围和内存事实，例如 `Zlength(l) == n`、`IntArray::full(a, n, l)` 以及所需的量化范围事实。

不要把 spec 写成“C 程序执行了这个递归模拟”。Spec 应描述输入/输出关系，而不是镜像实现。

## Assert 与循环不变量

中间 assert 与循环不变量应描述当前程序点为真的事实：

```c
/*@ Inv Assert
    exists l1 l2 l0,
      l == app(l1, l2) &&
      i == Zlength(l1) &&
      Permutation(l1, l0) &&
      increasing(l0) &&
      IntArray::full(nums, numsSize, app(l0, l2))
 */
```

对插入排序、冒泡排序、划分和分阶段处理，优先采用：

- 已处理/未处理拆分：`l == app(done, todo)`、`i == Zlength(done)`。
- 已处理部分性质：`increasing(sorted_done)`、`Permutation(done, sorted_done)`。
- 边界事实：`upperbound(pivot, left_part)`、`lowerbound(pivot, right_part)`、`strict_upperbound(x, l)`、`strict_lowerbound(x, l)`。
- 当前候选答案：`MinimizedMaxSegmentSum(l, m, res)`、`left <= res && res <= right`。
- 累积值：`ret == sum(sublist(0, i, l))`。

不要只为帮助后续证明而把不变量替换成 `mono_nondec(l)` 或 `mono_inc(idxs)` 等面向证明的谓词；只有当 spec 确实需要严格索引关系且不存在更合适的 annotation-facing 谓词时才这样做。

## 已有谓词

### ListLib 谓词

常见的 annotation-facing 名称：

- `increasing(l)`：非递减顺序。排序结果、已排序前缀和已排序后缀应优先使用它。
- `decreasing(l)`：非递增顺序。
- `strict_decreasing(l)`：严格递减顺序。
- `upperbound(x, l)` / `upper_bound(x, l)`：`x` 是所有元素的上界。
- `strict_upperbound(x, l)`：`x` 是严格上界。
- `lowerbound(x, l)` / `lower_bound(x, l)`：`x` 是所有元素的下界。
- `strict_lowerbound(x, l)`：`x` 是严格下界。
- `sum(l)`：轻量 `list Z` 求和，适用于 `sum(l)` 和 `sum(sublist(lo, hi, l))`。
- `Zlist_max(l, lo)`：旧式 list 最大值计算；新的优化 spec 应优先使用基于 `MaxMinLib` 构造的 case-level 谓词。

示例：

```c
Permutation(l1, l0) && increasing(l0)
strict_lowerbound(key, right_part)
ret == sum(sublist(0, i, l))
```

### MonotonicList 谓词

`mono_nondec`、`mono_noninc`、`mono_inc` 和 `mono_dec` 主要是面向证明的谓词，通常不要写进 annotation。

默认 annotation 选择：

- 普通升序：写 `increasing(l)`，不要写 `mono_nondec(l)`。
- 普通降序：写 `decreasing(l)`，不要写 `mono_noninc(l)`。
- 严格降序：写 `strict_decreasing(l)`。
- 严格升序：若不存在 annotation-facing 业务谓词，先考虑定义清晰的 case-level 语义谓词。只有 spec 确实描述严格递增索引序列时，才在 annotation 中暴露 `mono_inc(idxs)`。

### MaxMinLib 谓词

在 `formal_case_lib` 中用 `MaxMinLib` 定义问题语义，再让 C annotation 调用 wrapper 谓词。

推荐模式：在 `formal_case_lib` 中定义 `MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop` 这样的数学谓词，然后在 C annotation 中只声明并调用该名称。

`formal_case_lib` 一侧：

```coq
Require Import SimpleC.EE.QCP_demos_LLM.MaxMinLib.

Definition SegmentFeasible (l : list Z) (m cap : Z) : Prop := ...

Definition MinimizedMaxSegmentSum (l : list Z) (m ans : Z) : Prop :=
  min_value_of_subset
    (fun v => exists parts, PartitionMaxSegmentSum l m parts v)
    ans.
```

```c
/*@ Extern Coq (MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop) */

/*@ With (l : list Z)
    Require exists ans,
      MinimizedMaxSegmentSum(l, m, ans) &&
      0 <= ans && ans <= 1000000000 &&
      IntArray::full(arr, n, l)
    Ensure
      MinimizedMaxSegmentSum(l, m, __return) &&
      IntArray::full(arr, n, l)
 */
```

不要把漫长的搜索过程直接放进 annotation。应把“最大值”“最小值”或“最优值”定义成数学谓词，并在需要时由不变量维持它：

```c
exists res,
  left <= res && res <= right &&
  MinimizedMaxSegmentSum(l, m, res)
```

对于二分答案程序，把 spec 拆成：

- `CanX(l, args, cap)`：候选 `cap` 可行。
- `CannotX(l, args, cap)`：候选 `cap` 不可行。
- `OptimalX(l, args, ans)`：`ans` 是数学最优值。

C 循环维持 `left <= ans <= right`；证明侧 helper lemma 把 `CanX` / `CannotX` 与最优值边界连接起来。参见 `docs/correct-examples/binary-search-annotation.md`。

不要在每个 C 不变量中书写原始的 `min_value_of_subset` 或 `max_value_of_subset` 公式。应在 `formal_case_lib` 的业务谓词后封装它们，并且只向 C 暴露业务谓词。

### SumLib 谓词

对于普通 array/list 区间和，保持 annotation 简洁：

```c
ret == sum(sublist(0, i, l))
```

如果 spec 需要索引区间、有限集合或二维区域求和，先在 `formal_case_lib` 的业务谓词中封装 `SumLib` 语义，再从 annotation 调用该谓词。除非公式简短且确实提高可读性，否则不要把复杂有限集合公式放进每个不变量。

`formal_case_lib` 一侧：

```coq
Require Import SimpleC.EE.QCP_demos_LLM.SumLib.

Definition RangeContribution (l : list Z) (lo hi acc : Z) : Prop :=
  acc = sum_Z_range lo hi (fun i => Znth i l 0).
```

优先写：

```c
Prefix2DSum(grid, rows, cols, i, j, acc)
```

而不是在每个不变量中反复展开二维求和定义。

对于一维 list 求和，annotation 中优先使用轻量 list 形式：

```c
acc == sum(sublist(lo, hi, l))
```

只有 helper 自然需要有限区间、单调性、拆分或索引 map 时，才在证明中桥接到 `SumLib`。

## 设计新谓词与不变量

已有谓词不足时，应把新谓词设计成紧凑的数学关系，而不是可执行的 list 程序。

谓词设计规则：

- 直接逻辑陈述清晰时，避免用 `Fixpoint` 定义 list 性质；优先使用 `forall` / `exists`，不要定义递归遍历。
- 对 list 逐元素事实，使用基于 `Znth` 和 `Zlength` 的索引陈述，例如 `forall i, 0 <= i < Zlength l -> P (Znth i l d)`。
- 对区间事实，在 `sublist lo hi l` 上陈述，或对 `lo <= i < hi` 量化；不要把同一含义编码成自定义递归 list 扫描器。
- 只有确认 `Inductive` 的归纳原理和构造子便于预期证明后才使用它。构造子过多的语义谓词常使 generated goal 和证明搜索更重。
- 如果某性质天然包含多个字段或分支，考虑用带命名字段的 `Record` 封装事实。过多 inductive 分支会降低 Rocq 编译速度并使 goal 难以阅读。
- 新谓词应对小幅实现变化保持稳定。好的谓词描述数学状态，而不是产生它的具体循环步骤。

不变量书写规则：

- 对保持不变的性质优先使用简短 `forall` 事实，尤其是范围、边界、按索引排序和逐元素约束。
- 如果不变量选取一个元素，直接使用 `Znth i l d`。
- 如果不变量选取一个区间，直接使用 `sublist lo hi l`。
- 不要只为暴露一个元素而拆分 list。例如，当 `a == Znth i l d` 已表达相同观察时，应避免 `l == app(sublist(0, i, l), cons(a, sublist(i + 1, n, l)))` 这类形式。
- 只有算法确实分别维护所有权或排列关系各异的部分（如已处理前缀与未处理后缀）时才使用 `app` 分解；不要把它作为读取单个值的默认方式。
- 保持不变量可读。较小的不变量通常会产生较小的 generated goal，也能减少 Rocq 要编译和证明的无关结构。

推荐形式：

```c
forall i, 0 <= i && i < n => lower <= Znth(i, l, 0) && Znth(i, l, 0) <= upper
cur == Znth(i, l, 0)
window == sublist(lo, hi, l)
```

冒泡排序提供了一个良好的内层循环模式：

```c
exists a,
  Zlength(a) == n &&
  0 <= i && i < n - 1 &&
  0 <= j && j <= n - 1 - i &&
  Permutation(l, a) &&
  increasing(sublist(n - i, n, a)) &&
  (forall (p: Z) (q: Z),
    (0 <= p && p < n - i && n - i <= q && q < n) =>
    (Znth(p, a, 0) <= Znth(q, a, 0))) &&
  (forall (p: Z),
    (0 <= p && p < j) =>
    (Znth(p, a, 0) <= Znth(j, a, 0))) &&
  IntArray::full(arr, n, a)
```

该形式很简洁：已排序后缀写成 `increasing(sublist(n - i, n, a))`，未排序前缀与已排序后缀的边界写成索引上的 `forall`，当前内层循环最大值候选则直接写成 `Znth(j, a, 0)`。

避免：

```c
l == app(sublist(0, i, l), cons(a, sublist(i + 1, n, l))) &&
a == Znth(i, l, 0)
```

除非前缀、选中元素与后缀对算法分别具有实际意义。

对于冒泡排序内层循环，不要把不变量改写成通过分解 list 来反复暴露 `j` 的形式：

```c
a == app(left, cons(key, right)) &&
left == sublist(0, j, a) &&
right == sublist(j + 1, n, a) &&
increasing(sublist(n - i, n, a)) &&
...
```

这种形式增加了额外等式和 list 形状义务，却没有更好地解释数学事实。保持 list 完整，并使用 `Znth` / `sublist` 进行观察。

## 添加谓词之前

新增 `formal_case_lib` 定义前，先检查：

- `increasing` / `decreasing` 能否直接表达顺序性质？
- `upperbound` / `lowerbound` 能否直接表达边界性质？
- `sum(sublist(...))` 能否直接表达区间累积？
- 最大值、最小值或最优值是否应在业务谓词中用 `MaxMinLib` 封装？
- 区间、有限集合或二维求和是否应在业务谓词中用 `SumLib` 封装？
- 新定义表达的是数学语义，还是在复制 C 循环？
- 能否写成索引或区间上的 `forall` / `exists`，而不是 list `Fixpoint`？
- `Inductive` 定义会让证明结构更清晰，还是会引入过多分支？

只有已有谓词无法清晰表达预期语义时才添加新定义。新定义应提高 annotation 可读性和 spec 稳定性，而不是只服务于一个局部证明技巧。

## 避免的写法

不要在 C annotation 中写：

```c
/* 直接暴露面向证明的谓词。 */
mono_nondec(sorted_part)

/* 重复定义已有顺序谓词。 */
NondecreasingZList(l)

/* 把循环体镜像成递归状态机。 */
LoopStateAfterKSteps(...)
```

优先写：

```c
increasing(sorted_part)
decreasing(sorted_part)
lowerbound(pivot, right_part)
ret == sum(sublist(0, i, l))
MinimizedMaxSegmentSum(l, m, res)
```
