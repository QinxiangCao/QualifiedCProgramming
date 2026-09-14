# 精简 Predicate 示例

## 1. 单次数组扫描

目标：返回数组最大值。

最终结果直接复用 max_value_of_subset。循环进度是：

    best 是 sublist 0 i l 的最大值

若 max_value_of_subset 可以直接表达这句话，invariant 直接组合 sublist 和该接口，不再定义 PrefixMaximum。

Invariant 只需要：

    1 <= i <= n
    + best 是 sublist 0 i l 的最大值
    + IntArray::full(a, n, l)

读取 a[i] 前写实际访问需要的 i < n。数组资源已经给出的 Zlength l = n 和 0 <= n 不重复。

Plan：

    {
      "version": 2,
      "status": "ready",
      "function_specs": [
        {"name": "array_max", "meaning": "返回输入数组的最大值"}
      ],
      "loop_invariants": [
        {"location": "array_max: scan loop", "progress": "best 是已处理前缀的最大值"}
      ],
      "new_predicates": [],
      "vc_comparisons": []
    }

## 2. RMQ

最终语义只定义一次：

- RangeMaximum 表达查询区间最大值，内部复用已有最大值接口；
- SparseTableBuilt 引用 RangeMaximum，作为 build 与 query 的接口；
- BuiltLevels 引用 RangeMaximum，作为构造循环的唯一进度。

这个 RMQ 的 `build` 包含表清零、基础列和逐层构造，`query` 包含幂查找循环。下面先展示原 annotation，再给出分析、精简形状和八个定义的对应表。

### 原 C annotation

以下节选保留与 predicate 重复直接相关的字段，省略同一 assertion 中其他执行范围。

逐层构造的内层循环同时保存“旧层全部完成”和“当前层前缀完成”：

~~~c
/*@ Inv Assert
    exists st_l,
    1 <= j && j < K &&
    half == Power2(j - 1) &&
    len == Power2(j) &&
    len == half * 2 &&
    0 <= i && i <= n &&
    BuiltLevels(l, st_l, K, n, j) &&
    LevelPrefixBuilt(l, st_l, K, n, j, i) &&
    IntArray::full(arr, n, l) *
    IntArray::full(st, n * K, st_l)
 */
for (int i = 0; i + len <= n; ++i) {
  int a = st[i * K + j - 1];
  int b = st[(i + half) * K + j - 1];
  if (a >= b) {
    st[i * K + j] = a;
  } else {
    st[i * K + j] = b;
  }
}
~~~

query 的循环同时写出 pow 的范围并调用 LogSearchState：

~~~c
/*@ Inv Assert
    len == right - left + 1 &&
    1 <= len && len <= n &&
    0 <= k && k < K &&
    1 <= pow && pow <= len &&
    LogSearchState(len, k, pow) &&
    SparseTableBuilt(l, st_l, K, n) &&
    IntArray::full(st, n * K, st_l)
 */
while (pow * 2 <= len) {
  pow = pow * 2;
  k++;
}
~~~

### 原 Rocq predicate

三个构造 predicate 都重复 RangeMaximum，只在完成范围上不同：

~~~coq
Definition BaseColumnBuilt
    (l table : list Z) (K upto : Z) : Prop :=
  forall row,
    0 <= row < upto ->
    RangeMaximum l row (row + 1)
      (Znth (row * K) table 0).

Definition BuiltLevels
    (l table : list Z) (K n levels_done : Z) : Prop :=
  forall row level,
    0 <= row /\
    0 <= level < levels_done /\
    row + Power2 level <= n ->
    RangeMaximum l row (row + Power2 level)
      (Znth (row * K + level) table 0).

Definition LevelPrefixBuilt
    (l table : list Z) (K n level upto : Z) : Prop :=
  forall row,
    0 <= row < upto ->
    row + Power2 level <= n ->
    RangeMaximum l row (row + Power2 level)
      (Znth (row * K + level) table 0).

Definition LogSearchState (len k pow : Z) : Prop :=
  pow = Power2 k /\ Power2 k <= len.
~~~

### 分析

- BaseColumnBuilt 是 level = 0 时的当前层前缀。
- 旧 BuiltLevels 表示 level 之前的完整层。
- LevelPrefixBuilt 表示 level 的当前前缀。
- 三者可以合并成一个带 level 和 prefix 参数的 BuiltLevels。
- SparseTableBuilt 只固定 BuiltLevels 的完成参数，作为 build/query 接口保留。
- LogSearchState 只包装两个短关系，直接写进 invariant。
- ZeroedPrefix 不连接 SparseTableBuilt 或 query，清零循环只需要范围和数组资源。
- n/K 的容量界、n < Power2(K) 和查询区间界仍分别用于 C 安全、保持 k < K 和最终表下标；精简 predicate 不删除这些实际使用的条件。

### 精简后的 Rocq 形状

RangeMaximum 直接复用核心最大值 predicate：

~~~coq
From MaxMinLib Require Import MaxMin Interface.

Definition RangeMaximum
    (l : list Z) (lo hi ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun index => lo <= index < hi)
    (fun index => Znth index l 0)
    ans.
~~~

一个 BuiltLevels 同时表达完整旧层和当前层前缀：

~~~coq
Definition BuiltLevels
    (l table : list Z)
    (K n level prefix : Z) : Prop :=
  (forall row done_level,
      0 <= row /\
      0 <= done_level < level /\
      row + Z.pow 2 done_level <= n ->
      RangeMaximum l row (row + Z.pow 2 done_level)
        (Znth (row * K + done_level) table 0)) /\
  (forall row,
      0 <= row < prefix ->
      row + Z.pow 2 level <= n ->
      RangeMaximum l row (row + Z.pow 2 level)
        (Znth (row * K + level) table 0)).

Definition SparseTableBuilt
    (l table : list Z) (K n : Z) : Prop :=
  BuiltLevels l table K n K 0.
~~~

对应的 C Extern 只保留 RangeMaximum、BuiltLevels、SparseTableBuilt，以及 annotation 语法确实需要时的透明 Power2。

### 精简后的 C annotation 形状

内层构造循环只使用一个进度 predicate：

~~~c
/*@ Inv Assert
    exists st_l,
    arr == arr@pre && n == n@pre &&
    K == K@pre && st == st@pre &&
    1 <= n && n <= 100000 &&
    1 <= K && K <= 30 &&
    n * K <= 1000000 &&
    n < Power2(K) &&
    1 <= j && j < K &&
    half == Power2(j - 1) &&
    len == Power2(j) &&
    len == half * 2 &&
    0 <= i && i <= n &&
    BuiltLevels(l, st_l, K, n, j, i) &&
    IntArray::full(arr, n, l) *
    IntArray::full(st, n * K, st_l)
 */
~~~

query 循环直接写幂关系：

~~~c
/*@ Inv Assert
    st == st@pre && n == n@pre && K == K@pre &&
    left == left@pre && right == right@pre &&
    1 <= n && n <= 100000 &&
    1 <= K && K <= 30 &&
    n * K <= 1000000 &&
    n < Power2(K) &&
    0 <= left && left <= right && right < n &&
    len == right - left + 1 &&
    1 <= len && len <= n &&
    0 <= k && k < K &&
    pow == Power2(k) &&
    1 <= pow && pow <= len &&
    SparseTableBuilt(l, st_l, K, n) &&
    IntArray::full(st, n * K, st_l)
 */
~~~

| 当前定义 | 结果 |
|---|---|
| Power2 | 优先复用已有幂运算 |
| RangeMaximum | 保留，直接引用核心最大值 predicate |
| ZeroedPrefix | 删除 |
| BaseColumnBuilt | 合并到 BuiltLevels |
| BuiltLevels | 保留 |
| LevelPrefixBuilt | 合并到 BuiltLevels |
| SparseTableBuilt | 保留 |
| LogSearchState | 删除，短等式直接写 invariant |

精简后的引用关系只有：

    核心最大值 predicate
      -> RangeMaximum
      -> BuiltLevels / SparseTableBuilt
      -> build / query annotation

不要在 RangeMaximum 外继续增加 CellMaximum 或 LevelMaximum，也不要让 BuiltLevels 和 SparseTableBuilt 各自重新展开最大值定义。

Plan：

    {
      "version": 2,
      "status": "ready",
      "function_specs": [
        {"name": "build", "meaning": "建立每个有效单元都表示对应区间最大值的查询表"},
        {"name": "query", "meaning": "返回给定区间的最大值"}
      ],
      "loop_invariants": [
        {"location": "build: zero loop", "progress": "idx 个表单元已经经过清零扫描"},
        {"location": "build: base-column loop", "progress": "第 0 层前 i 行已经表示单元素区间最大值"},
        {"location": "build: outer level loop", "progress": "j 之前各层已经表示对应区间最大值"},
        {"location": "build: inner row loop", "progress": "j 之前各层和第 j 层前 i 行已经表示对应区间最大值"},
        {"location": "query: power loop", "progress": "pow 是当前不超过区间长度的二次幂"}
      ],
      "new_predicates": [
        {
          "name": "RangeMaximum",
          "meaning": "值是输入列表指定区间的最大值",
          "why_needed": "最终 query 语义和表中每个单元共同引用该区间性质"
        },
        {
          "name": "SparseTableBuilt",
          "meaning": "每个有效表单元满足 RangeMaximum",
          "why_needed": "build 与 query 需要同一个表接口"
        },
        {
          "name": "BuiltLevels",
          "meaning": "已完成层和当前层前缀满足 RangeMaximum",
          "why_needed": "构造循环在多层和当前前缀之间重复使用该进度"
        }
      ],
      "vc_comparisons": []
    }

Power2 只有在 annotation 语法需要一个可引用名称时列为新 predicate；可以直接写幂运算时不列。

## 3. 两层 DP

先确定最终输出的数学最优值。若 caller 不读取完整 DP table，顶层 Ensure 不承诺每个 cell。

外层循环进度：

    前 rows_done 行表示对应子问题的最优值

内层循环进度：

    已完成行保持正确，当前行前 cells_done 个 cell 正确

如果两句话可以用同一个带 rows_done 和 cells_done 参数的 predicate 清楚表达，只保留一个 predicate。不要分别定义 RowsDone、RowPrefixDone、CellCorrect 和 TableShape，再在 invariant 中全部叠加。TableShape 由数组资源与直接范围表达。

## 4. 判断是否需要新 predicate

逐项检查：

1. 它是否表示数学性质，而不是 C 控制状态？
2. 核心 predicate 的直接组合是否已经清楚？
3. 同一长公式是否在多个 spec、helper 或 invariant 中出现？
4. 删除一个参数后含义是否仍完整？
5. 所有使用位置是否引用同一个定义？

前两项不满足时不新增。只出现一次但名称直接对应题目概念时可以保留；只包装一个范围、等式或现有 predicate 时不保留。

## 5. Retry

直接比较 old manual 与 current manual 的命题内容：

    {
      "source": {
        "attempt": "case-vc-proving-r1:group_01",
        "name": "proof_of_query_entail_wit_3",
        "annotation_location": "query power loop exit"
      },
      "current": ["proof_of_query_entail_wit_3"],
      "old_gap": "退出状态缺少 pow <= len",
      "change": "把 pow <= len 直接加入 query loop invariant",
      "result": "resolved"
    }

缺口仍存在时 result 写 unresolved，并继续修改当前 attempt。
