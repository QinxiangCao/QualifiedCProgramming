# split_array_largest_sum 二分教学例子

这个目录放置 `split_array_largest_sum` 的 annotation 正例，用于指导 agent 处理“二分答案 + check 判定函数”的 direct proof。配套 C 例子是：

- `split_array_largest_sum.c`
- 正式来源：`QCP_examples/LLM_bench/Algorithms/split_array_largest_sum/split_array_largest_sum.c`
- formal 定义来源：`SeparationLogic/examples/LLM_bench/Algorithms/split_array_largest_sum/split_array_largest_sum_lib.v`

遇到相似 case 时，优先学习这里的规格拆分和 invariant 形状，不要把它当作可机械复制的 proof 脚本。

## 适用模式

这个例子覆盖的程序形状是：

1. 主函数对答案空间做二分。
2. 辅助 `check` 函数判断某个候选值 `cap` 是否可行。
3. `check` 的返回值具有单调性：某个 `cap` 可行时，更大的候选值也可行；不可行时，更小的候选值也不可行。
4. 主循环每轮根据 `check(mid)` 缩小 `[left, right]`，最终返回最小可行答案。

对这类程序，annotation 的核心不是复述二分代码，而是把三个数学层次分开：

- `check` 维护的前缀判定状态。
- 候选 `cap` 是否可行的全局性质。
- 主循环中真实答案与当前二分边界的关系。

## 为什么选择这些谓词

### `PrefixSplitState`

`check` 顺序扫描数组，维护：

- 已处理前缀长度 `i`
- 当前已经使用的段数 `cnt`
- 当前段的和 `cur`
- 所有已形成的段都不超过 `cap`

`PrefixSplitState(l, cap, i, cnt, cur)` 不是一份 Rocq 版 `check` 程序；它是扫描到前缀 `i` 时已经形成的数学状态。C 循环 invariant 把局部变量与这个性质绑定：

```c
0 <= i && i <= n@pre &&
1 <= cnt && cnt <= i + 1 &&
0 <= cur && cur <= cap@pre &&
PrefixSplitState(l, cap@pre, i, cnt, cur)
```

这样每个 loop step 只需要证明“读入下一个元素后，前缀性质保持”，而不是证明 C 和某个 Rocq 递归解释器同步运行。

### `CanSplit` / `CannotSplit`

`check` 函数的对外规格不应该暴露内部扫描细节。它只需要告诉调用方：

- 返回 `1` 时，`cap` 足够大，可以把列表分成不超过 `m` 段。
- 返回 `0` 时，`cap` 不足以完成这种划分。

对应 annotation 是：

```c
(__return == 1 => CanSplit(l, m, cap)) &&
(__return == 0 => CannotSplit(l, m, cap))
```

这让主循环可以把 `check(mid)` 的结果转化成二分边界更新依据。`check` 的内部 invariant 证明 `PrefixSplitState`，函数 `Ensure` 再把它封装成 `CanSplit` / `CannotSplit`。

### `PartitionMaxSegmentSum` / `MinimizedMaxSegmentSum`

主函数真正要证明的是“返回值是所有合法分段中最大段和的最小值”。这应当先用严格数学定义表达，而不是在 Rocq 中定义一个 `splitArrayLargestSum` 函数再证明 C 与它一致。

该例子在 lib 中使用 `MaxMinLib` 的数学接口：

- `MaxSegmentSum` 用 `max_value_of_subset` 描述某个分段里的最大段和。
- `PartitionMaxSegmentSum` 描述一个长度为 `m` 的合法分段及其最大段和。
- `MinimizedMaxSegmentSum` 用 `min_value_of_subset` 描述所有合法分段最大段和中的最小值。

这组定义的作用是给出问题本身的数学语义。C 程序要证明自己满足这个语义，而不是证明自己等价于另一份程序。

## 二分主循环 invariant

主循环的关键 invariant 是：

```c
exists res,
arr == arr@pre && n == n@pre && m == m@pre &&
1 <= n@pre && n@pre <= 100000 &&
1 <= m@pre && m@pre <= n@pre &&
Zlength(l) == n@pre &&
IntArray::full(arr, n@pre, l) &&
(forall (i : Z), (0 <= i && i < n@pre) => (0 <= l[i] && l[i] < 100000000)) &&
0 <= left && right <= 1000000000 &&
left <= right &&
left <= res && res <= right &&
MinimizedMaxSegmentSum(l, m, res)
```

这里的 `res` 是数学答案，不是程序变量。这个 existential 是二分循环的核心桥梁：

- 初始化时，由函数 `Require` 提供某个 `ans` 满足 `MinimizedMaxSegmentSum(l, m, ans)`，并且 `0 <= ans <= 1000000000`。
- 循环保持时，`res` 继续代表同一个数学答案；只证明边界更新后仍有 `left <= res <= right`。
- 循环退出时，`left == right` 与 `left <= res <= right` 推出返回值就是 `res`，从而满足 `MinimizedMaxSegmentSum(l, m, __return)`。

不要把 invariant 写成“当前二分循环执行了多少轮、下一步 mid 怎么算”的 Rocq 状态机。二分循环需要维护的是答案被边界夹住这一数学事实。

## `check` 性质如何连接二分边界

`check(mid)` 的返回值只说明候选值 `mid` 的可行性，主循环还需要 helper lemma 把它连接到最优答案 `res`：

- `CanSplit(l, m, mid)` 与 `MinimizedMaxSegmentSum(l, m, res)` 推出 `res <= mid`。因此 `ok == 1` 时可令 `right = mid`。
- `CannotSplit(l, m, mid)` 与 `MinimizedMaxSegmentSum(l, m, res)` 推出 `mid < res`。因此 `ok == 0` 时可令 `left = mid + 1`。

在当前 `formal_case_lib` 或后续 `group_worker_lib` helper 中，这个连接由类似下面的 lemma 承担：

- `minmax_can_lower_bound`
- `minmax_cannot_upper_bound`
- `partition_max_to_can_split`
- `can_split_to_partition_max`

annotation 中不需要把这些证明塞进 C 断言；它只要保留足够的纯事实和空间资源，让 VC 能调用这些 lemma：

- `MinimizedMaxSegmentSum(l, m, res)`
- `CanSplit(l, m, mid)` 或 `CannotSplit(l, m, mid)`
- `1 <= m <= Zlength l`
- 元素非负性
- `left <= res <= right`
- `mid` 的范围和整数边界

## Rocq 中不应做什么

不要走下面这条路线：

1. 在 Rocq 中定义一个递归函数或状态机来模拟 `check`。
2. 再定义一个递归函数来模拟二分主循环。
3. 在 C annotation 中追踪这些函数的执行结果。
4. 最后证明 C 程序和 Rocq 程序逐步一致。

这会把证明目标变成“两个程序一致”，而不是“C 程序满足最大段和最小值这个数学性质”。它也会让每次 annotation 或 C 局部控制流变化都牵动整套 Rocq 算法镜像。

正确做法是：

- 先用严格数学定义描述目标性质。
- 在 `check` 中用前缀状态证明判定性质。
- 在主循环中用边界 invariant 证明二分保持数学答案。
- 只把必要的连接证明写成 helper lemma；若它属于 proof-side bridge，则由 group-worker 在 `group_worker_lib` 中新增当前 group suffix helper，最后通过 vc-proving parent verify 合并。

## 写类似 case 前的 checklist

1. `check` 的返回值是否已经封装成 `CanX` / `CannotX` 这类判定性质？
2. 主问题是否已经用 `min_value_of_subset`、`max_value_of_subset` 或同等级的数学定义表达？
3. 主循环 invariant 是否包含“真实答案在当前 `[left, right]` 内”？
4. `ok` 分支是否分别有 lemma 把可行 / 不可行结论转化成 `res <= mid` 或 `mid < res`？
5. C annotation 是否仍在描述程序状态，而不是追踪一份 Rocq 版程序？

如果第 5 点失败，先回到 predicate-first 设计，不要进入 vc-proving。
