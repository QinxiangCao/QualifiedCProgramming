# Annotation 设计指南

本指南只说明设计判断。命令、写入和报告边界以 workflow 为准。

## 1. Spec 先于 annotation

先从题意写自然语言 spec，再写 Rocq spec、C function spec 和 loop invariant。

### 自然语言 spec

    Signature
      函数、输入类型和输出类型

    Preconditions
      输入范围、长度和输入之间的关系

    Output
      什么输出算正确

样例只用于确认下标、顺序和分支等歧义。题解、算法提示和 C 控制流不决定 Output。

输出唯一时使用 functional 形式，直接给出结果值。输出允许多个答案时使用 relational 形式，写 Valid inputs out。这个选择在自然语言 Output、Rocq Spec 和 C Ensure 中保持一致。

一份合适的顶层 spec 能用于另一种合理实现。若定义包含当前 loop locals、DP 转移、scratch table 构造顺序或一份重放 C 的 Fixpoint，把它改回题目中的数学关系。

题目隐含但没有作为函数输入给出的对象直接在 Spec 中用 exists 量化。

## 2. Rocq 表达

自然语言含义确定后再翻译：

- Pre inputs : Prop 表达输入条件；
- Spec inputs out : Prop 表达输出关系；
- helper definition 只在名称能清楚说明题意时保留。

常见输出与表达：

| 输出 | 表达 |
|---|---|
| 唯一值 | out = expression |
| 计数 | out = #(fun x => P x) |
| 最小值或最大值 | min_value_of_subset / max_value_of_subset |
| 任意合法答案 | Valid inputs out |
| 特殊返回值 | 直接写特殊值与正常值的分支 |
| 不同形状的结果 | 已有 Inductive、option 或 sum |
| 总有定义的操作序列 | apply_op 与 fold |
| 关系式操作序列 | 关系组合 |

数值使用 Z。有顺序和位置的对象使用 list；无顺序的选择使用集合谓词。逐元素条件优先使用 Forall；需要索引或两表对应关系时使用 Znth 或 Forall2。

## 3. 先复用核心 predicate

搜索顺序：

1. 当前 handoff 固定的 dependency；
2. 当前 canonical case lib；
3. 公共库；
4. 当前 case 中已经定义的数学 predicate。

常用接口：

| 需要表达的内容 | 优先复用 |
|---|---|
| C 数组资源 | IntArray::full、seg、undef_seg 及对应 family |
| list 长度、读取、切片、更新 | Zlength、Znth、sublist、replace_Znth |
| 每个元素或两表对应元素 | Forall、Forall2 |
| 成员、互异、重排 | In、NoDup、Permutation |
| 单调性 | 当前依赖已有的一套 increasing/decreasing 或 mono 系列 |
| 有限集合、选择和计数 | 集合谓词、#、已有 Finite |
| 求和 | sum、sum(sublist lo hi l)、SumLib |
| 最小值和最大值 | min_value_of_subset、max_value_of_subset |
| 图 | valid_vpath、reachable |

一个 case 的同类性质只选择一套已有接口。例如单调性统一使用当前依赖中的一套，不再为 annotation 创建另一套同义定义。

直接组合已有 predicate 可以清楚表达时，不新增 case-local predicate。以下写成原表达：

- In、Permutation、sum、单调性、最值和 reachable 的同义包装；
- 单个范围、等式或索引条件；
- InputValid、InputBound、SizeSafe 一类输入条件集合；
- 只保存临时变量、guard 或循环控制状态的 predicate；
- 模拟当前实现步骤的算法定义。

已有核心 predicate 的组合也不再逐层嵌套。例如直接写 `Permutation input output /\ increasing output`、`sum (sublist lo hi l)` 或已有最大值关系，不再定义只转发这些表达的 `SortedResult`、`RangeSumValue` 或 `PrefixMaximum`。

题目最终语义或跨函数共享接口需要名称时，只保留一层 case predicate：

    核心 predicate
      -> 一层必要的题目或接口 predicate
      -> Spec / helper / invariant

Helper、循环状态和 Ensure 直接引用这一层，不再增加第二层同义 wrapper。

## 4. 新 predicate 的条件

新 predicate 同时满足：

- 表达题目、helper 接口或循环中的明确数学性质；
- 核心 predicate 的直接组合不足以清楚说明；
- 名称能清楚说明题目或接口，或能替代多处相同的长公式；
- 参数只包含解释该性质所需的逻辑对象；
- 所有使用者引用同一个定义。

只使用一次但名称直接说明题目概念时可以保留。只包装一个范围、等式或已有 predicate 时不保留。

最终输出性质是主定义。Helper spec 和 Ensure 直接引用它；循环需要处理进度时，进度 predicate 也直接引用这一主定义：

    核心结果 predicate -> helper spec
    核心结果 predicate -> function Ensure
    核心结果 predicate -> 必要的进度 predicate -> loop invariant

同一性质不在 spec、helper、invariant 中分别展开或重新命名。

空间 ownership 由 IntArray、string、list 或结构体 predicate 表达。Pure predicate 只表达数学性质。范围、guard、overflow、数组读取绑定和必要的 @pre bridge 直接写在 C annotation。

## 5. 映射到 C function spec

- With 引入资源对应的逻辑值；
- Require 直接写输入范围、长度、overflow 条件和输入资源；
- Ensure 调用数学输出 predicate 并归还资源；
- 顶层函数直接连接题目 Spec；
- helper 只暴露 caller 使用的抽象结果。

输入大小、标量范围、元素范围和执行安全条件直接展开。不要创建 InputValid、InputValues、InputBound 或 SizeSafe 包装。

Workspace 只有在 caller 依赖其内容时才进入 helper 的对外数学语义。否则 Ensure 只归还资源并承诺题目要求的结果。

## 6. Loop invariant

每个循环先写一句数学进度。Invariant 只保留：

    进度
    + 下一次执行需要的范围和 overflow 条件
    + live resources
    + 必要的读取绑定和 @pre bridge
    + 已有或必要的新数学 predicate

Invariant 需要满足三点：

- 入口可以初始化；
- 一轮 body 后可以保持；
- guard 为假时可以推出下一阶段或 Ensure。

不要复制所有函数入口条件。IntArray::full、seg 等资源已经给出的长度与区间事实不重复；具体数组访问需要的下标范围仍写在 invariant。

读取 v = a[i] 后，后续需要逻辑值时保留 bounds、数组资源和 v = Znth i l default。只有区间拥有独立数学或空间含义时才拆 prefix、current、suffix。

每个循环前只有一条 Inv Assert。普通 Assert 只补 symbolic execution 无法确定且后续确实需要的状态；可按需放在 if 前，不放在 return 或 Inv Assert 前。

## 7. RMQ 精简示例

原 C annotation、原 Rocq definition、逐项分析和精简后代码见 [精简 Predicate 示例](internal-predicate-examples.md#2-rmq)。

RMQ 只需要少量稳定 predicate：

- RangeMaximum：区间最大值，内部复用已有最大值接口；
- SparseTableBuilt：build 与 query 共享的表语义，逐项引用 RangeMaximum；
- BuiltLevels：构造循环的唯一进度，表达已完成层和当前层前缀，继续引用 RangeMaximum。

这个 RMQ 的 `build` 依次执行表清零、基础列构造和逐层构造，`query` 用循环寻找不超过区间长度的二次幂。原 annotation 使用以下八个定义，其处理方式是：

| 当前定义 | 精简方式 |
|---|---|
| Power2 | 复用已有幂运算；annotation 语法需要名称时才保留透明定义 |
| RangeMaximum | 保留为唯一的区间最大值接口，内部直接引用已有最大值 predicate |
| ZeroedPrefix | 删除；清零循环直接写范围、安全条件、bridge 和 arr/st 资源 |
| BaseColumnBuilt | 并入 BuiltLevels |
| BuiltLevels | 保留为构造循环唯一进度 |
| LevelPrefixBuilt | 并入 BuiltLevels |
| SparseTableBuilt | 保留为 build 与 query 的共享表接口 |
| LogSearchState | 删除；直接写 pow = 2^k 与 pow <= len |

不要再定义 CellMaximum、LevelRangeMaximum 或其他只嵌套 RangeMaximum 的名字。SparseTableBuilt 和 BuiltLevels 直接引用 RangeMaximum；RangeMaximum 直接引用核心最大值接口。

关系为：

    已有最大值 predicate -> RangeMaximum
    RangeMaximum -> BuiltLevels
    RangeMaximum -> SparseTableBuilt
    BuiltLevels 在构造完成时推出 SparseTableBuilt
    SparseTableBuilt -> build/query function spec

可以删除或直接展开：

- 清零循环不需要 ZeroedPrefix，直接保留 idx 范围、n * K 安全条件、必要 bridge 和 arr/st 资源；
- BaseColumnBuilt 与 LevelPrefixBuilt 合并到 BuiltLevels；
- pow = 2^k 和 2^k <= len 直接写进 query invariant，不需要 LogSearchState；
- 幂运算复用已有定义；只有 annotation 语法确实需要名称时保留透明 Power2。

清零循环：

    未变化参数的必要 bridge
    + 1 <= n, 1 <= K, n * K <= 1000000
    + 0 <= idx <= n * K
    + arr、st 完整数组资源

构造循环：

    j / i 的必要范围
    + 下一次数组访问与运算条件
    + arr、st 资源
    + BuiltLevels

查询循环：

    len = right - left + 1
    + pow = 2^k
    + pow <= len
    + n / K / 容量、查询区间与 k / pow 的必要执行范围
    + SparseTableBuilt
    + st 资源

## 8. Witness

按以下顺序选择：

1. 输入唯一决定且有清楚表达时使用直接值；
2. 有限有序对象使用 list；
3. 对象天然是映射时再使用函数 witness。

保留 exists f 时明确有效域和约束，并复用已有构造接口。不要把有限序列默认改成高阶函数。

## 9. 返工位置

回 annotation 修改：

- premise 缺读取绑定、guard、overflow、资源或必要 @pre bridge；
- helper 使用的数学前提没有进入 spec 或 invariant；
- Ensure 只有 shape/range，没有输出语义；
- loop 退出无法连接下一阶段或 Ensure；
- predicate 重复已有核心接口，或只记录控制状态；
- predicate 无法初始化或保持。

留给 proving：

- 数学 predicate 已经正确暴露，只缺连接 lemma；
- sublist、replace_Znth、Permutation、sum、最值或算术事实需要证明。
