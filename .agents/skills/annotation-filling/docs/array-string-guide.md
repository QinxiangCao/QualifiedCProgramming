# Array 和 String 谓词

遇到连续数组、字符缓冲区、C 字符串或字符串字面量时，先使用 builtin 谓词，再判断是否需要在 `formal_case_lib` 中新增数学定义。

## 常用 array 谓词

常用模块：`IntArray`、`UIntArray`、`CharArray`、`UCharArray`、`ShortArray`、`UShortArray`、`Int64Array`、`UInt64Array`、`PtrArray`。

核心谓词：

- `TArray::full(p, n, l)`：地址 `p` 开始、长度 `n`、精确内容为 `l` 的数组。
- `TArray::seg(p, lo, hi, l)`：同一基址上 `[lo, hi)` 区间，精确内容为 `l`。
- `TArray::full_shape(p, n)` / `seg_shape(p, lo, hi)`：只描述可访问 shape。
- `TArray::undef_full(p, n)` / `undef_seg(p, lo, hi)`：未初始化数组或区间。
- `missing_i` family：策略打开单个元素时的中间形态，默认不手写。

数组读写通常需要显式 bounds，例如 `0 <= i && i < n`。

## 选型

选 `TArray::full(p, n, l)`：

- spec 或 invariant 要谈 `Znth`、`sublist`、`replace_Znth`、`Permutation`、`sum`、`sorted`。
- 函数返回值依赖元素语义。
- 原地修改后 postcondition 要精确说明修改后的列表。
- refinement / pure spec 明确以列表值作为抽象状态。

典型 annotation 线索：

```c
ret == sum(sublist(0, i, l))
Permutation(l, l1) && increasing(l1)
v == Znth(i, l, 0)
new_l == replace_Znth(i, v, l)
```

选 `TArray::full_shape(p, n)` 或 `seg_shape(p, lo, hi)`：

- 只关心内存存在、长度和可访问性。
- 程序读写元素，但目标不依赖具体值。
- postcondition 只要求目标 buffer 合法。

shape 谓词适合 memory-layout 或 buffer-exists goals。若后续需要 `sum(l)`、`Permutation`、`sublist` 或元素范围，shape 已经不够，必须用精确内容谓词。

选 `TArray::seg(p, lo, hi, l)`：

- 多游标 / 双指针算法。
- 同一数组被划分为前缀、当前区间、后缀。
- merge、partition、copy、window 等算法需要维护相邻区间。

典型形状：

```c
IntArray::seg(a, 0, i, left_part) *
IntArray::seg(a, i, j, middle_part) *
IntArray::seg(a, j, n, right_part)
```

当循环有多个游标 `i / j / k`，并且每个游标对应不同逻辑区间时，`seg` 通常比一个巨大 `full` 加纯 `sublist` 等式更稳。

未初始化后逐步写满：初始用 `TArray::undef_full(p, n)`，循环中维护已写前缀 `seg` / `seg_shape` 和未写后缀 `undef_seg`。离开函数或 local scope 前，应能看到完整 `full` 或 `undef_full`。

偏移指针作为新基址：若后续主要通过 `p + i * sizeof(T)` 访问 suffix，可直接用偏移指针作基址；若还要和原数组其他区间组合，`seg(p, i, n, suffix)` 通常更合适。

## C string 谓词

```coq
store_string : Z -> list Z -> Assertion
```

`store_string(p, s)` 表示可读写 C 字符串缓冲区。逻辑内容 `s : list Z` 不包含结尾 `0`，底层内存包含 `s ++ [0]`。当程序语义就是 C 字符串时优先使用它；若 proof 需要底层字符区间，可使用 `CharArray::full` / `CharArray::seg`。

## String literal 谓词

```coq
store_stringLit : Z -> string -> Assertion
GlobalStrings : (string -> Z) -> Assertion
```

`store_stringLit(addr, s)` 表示 string literal，不适合表示可写局部数组，如 `char a[] = "abc"`。`GlobalStrings(LitMap)` 表示字面量地址池，可拆出 `store_stringLit(LitMap("..."), "...")`。默认不假设不同字面量地址不同，除非当前 case spec 额外声明。

## 建议

- 普通 int / uint / ptr 数组按上面的 `full`、`seg`、`shape` 或 `undef_*` 选型。
- `char *` 表示 C 字符串且 proof 使用“不含终止符的逻辑内容”时，用 `store_string(p, s)`。
- 字符数组只是普通字节数组时，用 `CharArray::full` / `seg` / `undef_*`。
- 字符串字面量读取前需要 `GlobalStrings(LitMap)` 或已拆出的 `store_stringLit`。
- 不要把 Rocq `string` 直接当成 `list Z`；需要内存列表时使用对应转换函数。
- 数组谓词描述资源拥有关系，`Znth` 描述对逻辑列表某个位置的观察；不要用 `Znth` 替代数组谓词本身。
- 单元素读写后，同时保留 bounds、数组资源和当前值绑定，例如 `0 <= i < n`、`IntArray::full(a, n, l)` 和 `v == Znth(i, l, 0)`。
- 分段写入或双指针算法仍优先维护 `full` / `seg` / `undef_*` 等资源形态，再用 `sublist`、`replace_Znth`、`Znth` 描述内容变化。
- 不要预设存在统一的 `Zhth` 基础库；如果某个 case 自己提供类似观察 predicate，只把它当作局部接口，不要让 invariant 核心语义退化成操作该接口。

## `missing_i` 使用边界

`missing_i` / `missing_i_shape` / `undef_missing_i` 通常是策略打开单个元素时产生的中间形态，不是手写 annotation 的默认选择。

不要因为代码出现 `a[i]` 或 `a[i] = v` 就手写 `missing_i`。先写高层 `full`、`seg`、`shape` 或 `undef_*`，让 array strategies 自动拆开并写回。只有当 spec 真正需要表达“除第 `i` 个元素外的其余数组”时，才考虑直接暴露 `missing_i`。

## `Znth` 和高层性质

`Znth` 用来观察某个位置，数组谓词用来说明资源拥有关系。二者不要互相替代。

适合写 `Znth` 的位置：

- 数组 read 后绑定局部值。
- 当前候选元素、pivot、边界元素。
- `replace_Znth` 写回前后的连接事实。

不适合把 invariant 写成一长串孤立 `Znth` 等式。如果真正想表达的是“当前 `best` 是已处理前缀的最大值”或“当前区间满足 partition”，应定义业务 predicate，例如 `PrefixMaxState(sublist(0, i, l), best)` 或 `PartitionedAround(l, lo, mid, hi, pivot)`。

若 proof 中发现必须新增基础 array/string memory semantics，先确认 builtin 是否已有；若 annotation 选错谓词，应回到 annotation 修正。
