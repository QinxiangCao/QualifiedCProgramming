# Annotation 中的纯命题谓词

本文件说明纯命题、有限量化、唯一 witness 与高阶 existential 的选型。Plan 只记录当前 case 实际新增的 predicate，完整定义以 case lib 为准。

本指南只用于 annotation 阶段：如何在 C annotation 与 case-level spec 中选择和书写已有的纯命题谓词。Rocq 证明侧的展开、桥接、改写和 helper lemma 属于 `group-worker-proving`。

核心规则：书写程序必须维持的数学事实。优先使用已有语义谓词，不要只为方便证明而暴露面向证明的结构，也不要在 `formal_case_lib` 中重复定义已有谓词。

结果与进度 predicate 的范围/资源边界、指定库的必用规则，以[知识规则 §0–2、§5–6](spec-and-contract-knowledge.md)为准；下文示例沿用这些约束。

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
      1 <= numsSize && numsSize <= 50000 &&
      IntArray::full(nums, numsSize, l)
    Ensure
      exists l1,
      Permutation(l, l1) &&
      increasing(l1) &&
      IntArray::full(__return, numsSize, l1)
 */
```

选择规则：

- 排序结果：写 `Permutation(l, l1) && increasing(l1)`；结果降序时写 `decreasing(l1)`。
- 求和结果：写 `__return == sum(l)`；在循环中维持 `ret == sum(sublist(0, i, l))` 等事实。
- 最大值、最小值或最优值：必须使用 `MaxMinLib` 的 `min_value_of_subset` / `max_value_of_subset`，不自定义 `IsMinimum` / `IsMaximum` 等同义接口；题目或跨函数接口需要名称时，保留一层直接复用库语义的 case predicate。
- 仍要陈述算法真正需要的元素范围和内存事实；`IntArray::full(a, n, l)` 已经包含 `Zlength(l) == n` 与 `0 <= n`，不要重复。
- 输入大小、元素范围和 safety 条件直接展开在 `Require` 中，不用 `SizeSafe`、`InputValues`、`InputValid`、`InputBound` 一类 predicate 包装；与下标无关的元素范围使用 `Forall`。结果和进度 predicate 都不混入这些前提或 ownership；`Ensure` 的数学部分只承诺最终输出，资源单独归还。

不要把 spec 写成“C 程序执行了这个递归模拟”。Spec 应描述输入/输出关系，而不是镜像实现。

## Assert 与循环不变量

中间 assert 与循环不变量应描述当前程序点为真的事实：

```c
/*@ Inv Assert
    exists l1 l2 l0,
      nums == nums@pre && numsSize == numsSize@pre &&
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
- `sum(l)`：来自 `AUXLib.ListLib` 的轻量 `list Z` 求和，适用于 `sum(l)` 和 `sum(sublist(lo, hi, l))`；不要与 `SumLib.Sum.sum P f` 混用。
- `Zlist_max(l, lo)`：旧式 list 最大值计算；新 spec 的最值性必须使用 `MaxMinLib` 的 `min_value_of_subset` / `max_value_of_subset`，必要的 case predicate 也直接复用该语义。

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
- 严格升序：先使用当前依赖已有的严格单调接口；只有 spec 确实描述严格递增索引序列时使用 `mono_inc(idxs)`，不再定义同义 case predicate。

### MaxMinLib 谓词

最值性必须使用 `min_value_of_subset` / `max_value_of_subset`。题目输出需要一个名称时，在 `formal_case_lib` 中保留一层问题 predicate，并让它直接引用 `MaxMinLib`；C annotation、helper 和 invariant 都调用这一名称，不再增加嵌套 wrapper。

推荐模式：在 `formal_case_lib` 中定义 `MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop` 这样的数学谓词，然后在 C annotation 中只声明并调用该名称。

`formal_case_lib` 一侧：以下片段沿用示例库的 `PartitionMaxSegmentSum : list Z -> Z -> Z -> Prop`，只展示最值层。它的候选集合是合法分段的最大段和值，不包含输入范围或 C 安全条件。

```coq
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import MaxMinLib.MaxMin.

Definition MinimizedMaxSegmentSum (l : list Z) (m ans : Z) : Prop :=
  min_value_of_subset Z.le
    (fun v : Z => PartitionMaxSegmentSum l m v)
    (fun v : Z => v)
    ans.
```

比较关系、候选集合、度量函数和结果四项不可省略。候选可能为空的题目另按输出格式保留 sentinel / `NO` 分支。

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

C 循环维持 `left <= ans <= right`；证明侧 helper lemma 把 `CanX` / `CannotX` 与最优值边界连接起来。参见 [二分答案正例](examples/binary-search-answer.md)。

复杂且重复的最值公式需要题目名称时，用这一层业务 predicate，避免在每个 C invariant 中展开。直接调用库接口已清楚时，不为隐藏调用再加 wrapper。

### SumLib 谓词

对于普通 array/list 区间和，保持 annotation 简洁：

```c
ret == sum(sublist(0, i, l))
```

索引区间、有限集合或二维区域求和必须按签名复用 `sum_range` / `sum` / `sum_set_R`；区间枚举使用 `Zrange`，不自行递归定义。复杂且重复的数学概念需要名称时，在 `formal_case_lib` 中保留一层直接复用这些接口的定义，避免在每个不变量中展开。

`SumLib.SumLib` 是有限集合求和库总入口；下例使用现有 `SpecHelpers` 提供的 `sum_range`，该模块也导出所需的整数、列表与有限集合接口。`[lo, hi)` 的右端点对应 `hi - 1`，表达式直接用于结果或累积值等式，不新增只包装等式的 `RangeContribution`：

```coq
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Open Scope Z_scope.

Check (fun (l : list Z) (lo hi : Z) =>
  sum_range lo (hi - 1) (fun i : Z => Znth i l 0)).
```

也可使用 `SumLib.Sum.sum (fun i : Z => lo <= i < hi) (fun i => Znth i l 0)`；该区间形状由 `SumLib.ZRange` 提供 `Finite` instance。`sum_set_R P f` 则需要 `Finite P` 与实数值 `f`。使用 `Znth` 的有效域条件仍由上下文提供。List 求和使用 `AUXLib.ListLib.sum`，不能因同名导入而误用 finite-set `sum P f`。

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

### Relation 的自反传递闭包

零步或多步 relation step 使用 `clos_refl_trans`，不自定义递归 `Reachable`、执行链或 path `Inductive`。当前仓库的接口可明确写为：

```coq
Require Import Coq.ZArith.ZArith.
Require Import SetsClass.RelsDomain.

Check (fun (step : Z -> Z -> Prop) =>
  SetsClass.RelsDomain.clos_refl_trans step).
```

它包含零步的 identity 与任意有限步；固定次数的 relation composition 不能替代该闭包。图路径语义仍复用类型匹配的 `valid_vpath` / `reachable`，不与标准库同名闭包接口混淆。

## 设计新谓词与不变量

已有谓词不足时，应把新谓词设计成紧凑的数学关系，而不是可执行的 list 程序。

谓词设计规则：

- 直接逻辑陈述清晰时，避免用 `Fixpoint` 定义 list 性质；优先使用 `forall` / `exists`，不要定义递归遍历。
- 与下标无关的 list 逐元素事实使用 `Forall P l`，不写 `forall i, 0 <= i < Zlength l -> P (Znth i l d)`；两表对应元素关系使用 `Forall2`。
- 对有效片段上的逐元素事实使用 `Forall P (sublist lo hi l)`；真正依赖位置或跨下标关系时才保留 guarded indexed quantification，不自定义递归 list 扫描器。
- `Inductive` 仅按知识规则 §1.4 的输出类型边界选用；不因证明方便而新建 operation chain、reachability 或普通值 wrapper。
- 多字段 predicate 或 `Record` 只有在表达明确数学概念时才保留；不得用它隐藏输入范围、容量、安全条件或空间 ownership。
- 新谓词应对小幅实现变化保持稳定。好的谓词描述数学状态，而不是产生它的具体循环步骤。

不变量书写规则：

- 只保留后续需要的范围并直接列出；与下标无关的逐元素约束使用 `Forall`，位置或跨下标约束才使用 guarded `forall`，已有单调性直接复用对应库。范围与资源不进入进度 predicate。
- 如果不变量选取一个元素，直接使用 `Znth i l d`。
- 如果不变量选取一个区间，直接使用 `sublist lo hi l`。
- 不要只为暴露一个元素而拆分 list。例如，当 `a == Znth i l d` 已表达相同观察时，应避免 `l == app(sublist(0, i, l), cons(a, sublist(i + 1, n, l)))` 这类形式。
- 只有算法确实分别维护所有权或排列关系各异的部分（如已处理前缀与未处理后缀）时才使用 `app` 分解；不要把它作为读取单个值的默认方式。
- 保持不变量可读。较小的不变量通常会产生较小的 generated goal，也能减少 Rocq 要编译和证明的无关结构。

推荐形式：

```c
Forall(Z::le(lower), l) && Forall(Z::ge(upper), l)
cur == Znth(i, l, 0)
window == sublist(lo, hi, l)
```

冒泡排序提供了一个良好的内层循环模式：

```c
exists a,
  arr == arr@pre && n == n@pre &&
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
- 最值是否直接使用 `MaxMinLib` 的 `min_value_of_subset` / `max_value_of_subset`，必要的业务 predicate 内部也只复用该语义？
- 求和、区间枚举与闭包是否复用了签名匹配的 `sum_range` / `sum` / `sum_set_R`、`Zrange`、`clos_refl_trans`？
- 新定义表达的是数学语义，还是在复制 C 循环？
- 是否已用 `Forall` / `Forall2` 表达逐元素/对应关系，只对确需位置的性质保留 indexed quantification？
- 新 predicate / `Record` 是否只包含目标数学性质，且没有混入输入范围、执行安全条件或资源？

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
