# Array 与 String 谓词

遇到连续数组、字符缓冲区、C 字符串或字符串字面量时，先使用 builtin predicate；只有独立且重复的数学性质再进入 `formal_case_lib`。

## 常用 array 谓词

常用模块：`IntArray`、`UIntArray`、`CharArray`、`UCharArray`、`ShortArray`、`UShortArray`、`Int64Array`、`UInt64Array`、`PtrArray`。

核心谓词：

- `TArray::full(p, n, l)`：地址 `p` 开始、长度 `n`、精确内容为 `l` 的数组。
- `TArray::seg(p, lo, hi, l)`：同一基址上 `[lo, hi)` 区间，精确内容为 `l`。
- `TArray::full_shape(p, n)` / `seg_shape(p, lo, hi)`：只描述可访问 shape。
- `TArray::undef_full(p, n)` / `undef_seg(p, lo, hi)`：未初始化数组或区间。
- `missing_i` family：策略打开单个元素时的中间形态，默认不手写。

数组读写通常需要显式 bounds，例如 `0 <= i && i < n`。

`TArray::full(p, n, l)` 本身已经给出 `Zlength(l) == n` 和 `0 <= n`；`TArray::seg(p, lo, hi, l)` 等资源也已经给出自己的区间与长度信息。不要在同一 spec 或 annotation 中重复这些事实。这里说的访问 bounds 是当前下标是否合法，与资源已经给出的数组长度不是一回事。

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

不适合把 invariant 写成一长串孤立 `Znth` 等式。“当前 `best` 是已处理前缀的最大值”用 `sublist` 与 `MaxMinLib` 的 `max_value_of_subset` 表达；partition 优先组合 `Forall`、`sublist` 和现有边界 predicate。必要的业务 predicate 内部同样复用指定库语义，不混入资源、输入范围或执行安全条件。

若 proof 中发现必须新增基础 array/string memory semantics，先确认 builtin 是否已有；若 annotation 选错谓词，应回到 annotation 修正。

## 可增长 vector

含元素个数、capacity 与元素 buffer 指针的 struct 是可增长 vector，用 vector 库 `Rocq/examples/Applications_human/dynvec_lib.v` 中的 `DynVec` 与 `VecArray` 描述，不手写其字段谓词。现有 instance `Veci`、`Vecp` 与 `VecpArray`（`vecp_t` 数组）在 `Rocq/examples/Applications_human/minisat/vec_qcp_lib.v`，供已 include `QCP_examples/Applications_human/minisat/vec_qcp.h` 的 target C 使用。该头文件声明 C struct `veci_t`（int 元素）与 `vecp_t`（指针元素）以及 client 所见的操作 contract。

| 视图 | 含义 | 使用场景 |
|---|---|---|
| `Veci::rep(v, l)` | `v` 存 `l`；buffer 与 capacity 隐藏 | 默认；任何可能增长 vector 的调用；嵌在更大的 struct 谓词中 |
| `Veci::rep_ptr(v, p, l)` | 另外命名 buffer `p` | `veci_begin` 之后原地遍历或写元素 |
| `Veci::shell(v)` | 三个未初始化字段 | `*_new` 之前、`*_delete` 之后 |

`Vecp::` 同理。暴露 capacity 的 `rep_at` 与 strategies 打开 buffer 时留下的 struct `header` 都不出现在 annotation 中；annotation 只用 `rep`、`rep_ptr` 与 `shell`，capacity 始终隐藏。内容是 `list Z`（int 值或 Z 地址），用现有 list 操作描述变化：push 得到 `rep(v, app(l, cons(x, nil)))`，原地写为 `replace_Znth(j, w, l)`，resize 为 `sublist(0, k, l)`。`rep` 与 `rep_ptr` 已蕴含 `0 <= Zlength(l) <= INT_MAX`，不要重述。`vec_qcp.h` 的 push 不要求长度上界。

`vecp_t` 数组的整张表直接写成 `VecpArray::full(tbl, m, ls)`，表长等 case 事实写成其旁边的 case predicate。`vec_qcp.strategies` 的 table 规则自动处理单个 slot：在 `0 <= i < n` 可证时，代码需要 `Vecp::slot(tbl, i)`、别名 `w == Vecp::slot(tbl, i)` 或 `&tbl[i]` 的 `Vecp::rep`、`rep_ptr` 或字段时取出该 slot，留下 `VecpArray::missing_i`，slot 回到 `Vecp::rep` 后折回 `full`（内容改变时为 `replace_Znth`）。这些规则不覆盖的形状手写：两个 slot 同时取出写 `VecpArray::missing2`（代码在两次折回之间更新同一张表的两个 slot 时），slot 跨循环保持取出时在 Inv Assert 中写 `Vecp::rep_ptr(...) * VecpArray::missing_i(tbl, i, 0, m, ls)`，以及不从 slot 0 开始的 `missing_i`。body 为 `VecpArray.full` 的 case 表谓词（table 规则需要一条打开它的 strategy 规则）与不从 slot 0 开始的 segment（`vec_qcp_def.h` 不导出 `VecpArray::seg`）交回 main。`DYNVEC.md` 第 5 节列出这些情形及示例。未初始化尾部用 `VecpArray::undef_seg`。表长用 `m` 等 ghost 表达式界定，不用 `Zlength(ls)`。`missing_i` 与 `missing2` 是仅有的 hole 形状。

- target C 必须已有 `#include "vec_qcp.h"`。不得把 `vec_qcp.h`、`vec_qcp_def.h` 或 `vec_qcp.strategies` 复制进 case，也不重复 `vec_qcp_def.h` 已有的 `Extern` 声明。`formal_case_lib` 中的 case predicate 提到 vector 时，在其中写 `From SimpleC.EE.Applications_human.minisat Require Import vec_qcp_lib.`。dune 模式下，该 import 要求 case 的 dune `coq.theory` 就是或列出 `SimpleC.EE.Applications_human`（即 case 位于 `Rocq/examples/Applications_human` 下）；其他位置的 case 把它交回 main。
- 允许 case 专用适配：在库谓词旁表达 case 事实（例如表长）的纯 case predicate、slot 下标函数或纯下标事实。不允许：针对 size/cap/ptr 字段 cell 或 buffer 的谓词、只改名的库谓词别名、库 lemma 的 case 副本。
- 其他 vector struct（struct 或字段名不同、元素类型不同，或程序自带 push/grow 代码）需要新的 `DynVec` instance、对应 strategies 与单独验证的操作单元，由 main 编写。在 `agent_output.md` 中记录 struct 与字段名、元素类型、client 调用的操作及其 contract（init 为 `shell` 到 `rep(v, nil)`，push 为 `rep(v, l)` 到 `rep(v, app(l, cons(x, nil)))`）、裸 `malloc`/`realloc`/`free`/`abort` 调用、可能 `int` 溢出的增长算术，以及 client 直接访问的字段或取地址的局部 vector struct（新 strategies 需要相应规则），然后以 infrastructure blocker 停止（workflow §7）。增长策略本身（`cap + 8`、倍增）不受限制，因为 `rep` 隐藏 capacity。
- `DynVec` 无法表达的布局（size 或 capacity 不是 C `int`、`begin`/`end`/`cap_end` 指针三元组、额外字段、内联 buffer）属于库缺口。按同样方式交回并写明不匹配之处，不写针对字段的 case predicate。

错误：

```c
store(&(v->size), n) * store(&(v->cap), c) * store(&(v->ptr), p) *
IntArray::seg(p, 0, n, l) * IntArray::undef_seg(p, n, c)
```

正确：

```c
Veci::rep_ptr(v, p, l)
```
