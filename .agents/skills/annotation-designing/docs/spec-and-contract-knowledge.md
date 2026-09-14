# Spec 与 Function Contract 知识规则

本文件只规定最终 Rocq spec 与 QCP function contract 的知识性要求，不增加现有 workflow 之外的任何流程要求。执行顺序和写入边界仍以 workflow 为准。

下文区分三个层次：

- `Pre` / `Spec` 与 case-level helper 描述题目数学语义；
- `Require` / `Ensure` 把该语义连接到 C 参数、pre-state / post-state 和 ownership；
- `Assert` / `Inv Assert` 描述中间程序点，不改变顶层输入输出关系。

## 1. 类型与编码

### 1.1 统一使用 `Z` 和 Z-indexed list 接口

数学整数、长度和下标使用 `Z`。不要在新 spec 或 helper 中使用 `nat`、`length`、`nth` 或 `nat` subtraction；使用 `Zlength`、`Znth`、`sublist` 和 `replace_Znth`。

### 1.2 字符是源字符的十进制编码

字符序列使用 `list Z`，二维字符网格使用 `list (list Z)`。不要使用 `ascii`、`list ascii`、`%char`、`ascii_dec`、`nat_of_ascii`、`ascii_of_nat` 或 `CharCode` 一类 wrapper。

是否使用字符码由 input format 决定，而不是由字符长得像什么决定：

| input format | 表示 |
|---|---|
| 一行字符串 `s` | 源字符码，例如 `'0' = 48`、`'1' = 49` |
| 一行 `n` 个整数 | 数值 `Z`，例如 `0`、`1` |

字符串中的数字仍是字符码。不要把 `'0'` / `'1'` 私自重编码为 `0` / `1`，也不要把 `S` / `F`、`<` / `=` / `>` 等源符号改成私有 alphabet。直接写真实编码，并可在注释中说明，例如 `S = 83`、`F = 70`、`< = 60`；不要再定义 `ch_zero`、`ch_one` 一类常量 alias。字符型输出遵循同一规则。

### 1.3 数值数据不因为取值为 0/1 就变成 `bool`

题目以整数给出的 flag、digit、matrix entry 或 state 继续使用 `Z`。只有题目本身定义了 Boolean 语义对象或逻辑运算时才使用 `bool`，并使用 `xorb`、`negb`、`Bool.eqb` 等 Boolean 运算，不用整数加法后 `mod 2` 模拟。

二选一的打印 verdict（如 `YES` / `NO`）使用题目约定；没有其他约定时使用 `out : Z`，正向为 `1`、负向为 `0`。题目规定的 sentinel 保持原值，例如“长度或 `-1`”仍用一个 `Z` 输出并对两个分支作析取，不创建 `bool` 或只为包装普通值而创建 `Inductive`。

### 1.4 `Inductive` 与 collection 表示

不要为输入 alphabet、operation chain、reachability 或普通值 wrapper 新建 `Inductive`。只有输出的不同分支携带真正不同的 payload shape，且现有 sentinel、`option` 或 `sum` 都不能更清楚地表达时，才考虑最小的 output-only datatype；优先复用已有类型。

有内在顺序的 sequence 使用 `list`。subset、selection 或其他无序选择使用集合谓词 `A -> Prop`，并用 `#` / `sum` 表达 cardinality 或 aggregation；不要用 `list Z` 加 `NoDup` 冒充无序集合。

## 2. 算术与库接口

### 2.1 只在真实 residue / wrap-around 语义中使用 `mod`

整除写 `(d | n)`，不整除写 `~ (d | n)`；parity 写 `(2 | n)` 或 `exists k, n = 2 * k` / `n = 2 * k + 1`。圆环上相对位置等能直接写成 `a + n / 2 = b \/ b + n / 2 = a` 的关系也不用 `mod`。只有题目契约本身确实描述 residue class 或 wrap-around，且没有更直接的关系时才使用 `mod`。`(d | n)` 与 `/\`、`\/` 组合时加括号。

### 2.2 复用极值、单调性、量化、求和与可达性

- 最小值和最大值使用 `min_value_of_subset` / `max_value_of_subset`，不手写 `IsMinimum` / `IsMaximum`，也不借 classical choice API 合成极值。候选集合可能为空时，覆盖题目要求的 sentinel / `NO` 分支；只写空集合上的 extremum 会让 `Spec` 不可满足。
- 不手写 all-pairs / adjacent `Znth` 单调性，也不另用 stdlib `Sorted` 建同义接口。使用当前 dependency 已采用的 canonical family；已有 `mono_inc` / `mono_nondec` / `mono_dec` / `mono_noninc` 时直接用它们，annotation-facing library 已固定 `increasing` / `decreasing` 时保持该现有 family。一个 case 不混用同义 family。
- 与 index 无关的逐元素性质使用 `Forall`；对应位置关系使用 `Forall2`；rearrangement 使用 `Permutation`；membership 使用 `In`。真正依赖 index 的条件，例如 `p_i < i`，必须保留 indexed quantification，不能弱化为 value-only `Forall`。
- 默认不写 custom `Fixpoint` 来重新实现 list sum、range enumeration 或 state fold。使用 `sum_range` / `sum` / `sum_set_R`、`Zrange`、`map`、`fold_left` / `fold_right`；partial 或 relational transition 使用已有 one-step relation、`Rels.id` 和 relation composition。
- 不自定义递归 `Reachable` / path `Inductive`。使用与 vertex type 匹配的 `valid_vpath` / `reachable`，simple path 另加 `NoDup`；适用时使用 `clos_refl_trans` 或 relation composition。

### 2.3 避免只为下标 scaffolding 保留 `Zrange`

`Zrange lo hi` 表示 half-open interval `[lo, hi)`：`Zrange 0 n` 是 `0 .. n-1`，`Zrange 1 (n+1)` 是 `1 .. n`。可以直接写 shifted range 或 list operation 时，不要再套 identity / shift `map`：

| 冗余表达 | 直接表达 |
|---|---|
| `map (fun i => i + k) (Zrange 0 n)` | `Zrange k (n + k)` |
| `map (fun i => i) (Zrange 0 n)` | `Zrange 0 n` |
| `map (fun i => f (Znth i a 0)) (Zrange 0 (Zlength a))` | `map f a` |
| 同下标读取 `a` 与 `b` 后计算 | 在 `combine a b` 上 `map` |

只有 `i` 还参与 shifted read、index arithmetic 或 index predicate 时才保留 range enumeration。

### 2.4 有限集合表达必须真的可 elaboration

每个 `#P` 和 `sum P f` 都必须能得到实际的 `Finite P` instance。保持 library 能识别的 predicate shape，并引入提供该 instance 的已有 module。数学上有限但 Rocq 无法 elaboration 的写法不是可交付 spec。

### 2.5 `Znth` 的负下标不会返回 default

`Znth n l d` 经由 `Z.to_nat n` 取下标；负数会映射到 `0`，所以 `Znth (-1) l d` 读取第一个元素，而不是 `d`。判断 read 是否安全时看 enclosing precondition / quantifier 是否允许负下标，不要只看表达式里是否有 subtraction。

若上下文可能令下标为负，必须 guard 读取或收紧量化范围；若上下文已经推出非负，不增加冗余 guard。例如：

```coq
(* i = 0 时 i - 1 为负，错误地 alias 第一个元素。 *)
forall i, 0 <= i < Zlength l -> P (Znth (i - 1) l 0)

(* guard 读取。 *)
forall i, 0 <= i < Zlength l ->
  P (if 0 <=? i - 1 then Znth (i - 1) l 0 else 0)

(* 或排除不需要的边界值。 *)
forall i, 1 <= i < Zlength l -> P (Znth (i - 1) l 0)
```

## 3. Definition hygiene

### 3.1 删除没有语义增量的名字

不要保留以下 definition：

- trivial type alias，如 `Definition Answer : Type := Z`；
- 已有 predicate alias，如 `Definition Occurs a x := In x a`；
- bare range wrapper，如只表示 `1 <= x <= n` 的 `OnCircle`；
- 重新计算 `Spec` 已经绑定值的 helper；
- 用 sign multiplier 等 opaque gadget 代替直接结果分支；
- 在参数与顺序完全相同的情况下只把 `Pre` / `Spec` 改名为 `ReturnedResult` 的 identity bridge。

表示转换 bridge 只有在确实完成 decoding / encoding、type 或 layout conversion、tag / sentinel interpretation、composite reconstruction 或 pre-state / post-state selection 时才有意义。删除 identity / unused bridge 时，也删除其 transitively unused declaration、import 和 mapping entry；不要借 cleanup 修改 frozen `Pre` / `Spec`。

### 3.2 不写立即应用的 lambda

不要把一个 lambda 放在 head position 后立即应用；直接调用目标函数。若 lambda 只用于 type ascription，把类型写到 definition 的参数上。作为高阶函数参数传递的 lambda（例如 measure `fun x => x`）可以保留。

```coq
(* 不要写。 *)
Definition D (x : Z) : Prop := (fun Q : Z -> Prop => Q x) P.

(* 直接写。 *)
Definition D (x : Z) : Prop := P x.
```

### 3.3 也不要把多个概念硬塞进一个 definition

删除 wrapper 不等于把所有内容 inline 成一个巨大 term。出现以下任一情形时应拆分：

- 同一非平凡 sub-expression 出现两次；
- 一个 body 同时混合 validity condition 与 measure；
- inner `exists` 的 witness 带有自己的一组条件；
- 题目已经为该概念提供了清楚名称。

例如拆成 `StreetWalk ... path` 与 `WalkLength path`，然后写 `exists path, StreetWalk ... path /\ v = WalkLength path`。形如 `v = expression` 的 concept 应是 value-producing function，而不是只为包住等式的 `Prop`。

一个 helper 应表达题目命名的概念、跨函数接口或重复的非平凡公式。可用朗读测试：若 definition 需要三句话才能说明，它通常包含三个概念。

## 4. 对题意的忠实性

### 4.1 不用需要证明的派生 characterization 代替原题

不要把 spec 写成 closed form、求解后的 case split 或必须先证明才知道等价的 simplification。直接量化题目对象；未显式作为输入给出的 background quantity 用 `exists` 及其定义性质绑定，而不是计算式替代。

### 4.2 保留 index、order 和 correspondence

- `p_i < i` 一类 indexed bound 保持 indexed；value-only bound 不是同一个 spec。
- common prefix、walk、operation order 和 corresponding-position constraint 不得退化成 unordered membership 或 set intersection。
- 输入和输出是 ordered sequence 时，不要为了集合接口丢失顺序或重复元素信息。

### 4.3 覆盖所有输出分支并保持 totality

`output_format` 的每个分支都必须出现在 `Spec`。对每个满足 `Pre` 的输入，至少存在一个满足 `Spec` 的输出，包括 `-1`、`NO`、empty output 或题目规定的其他 exceptional branch。候选集合可能为空时，不能只写 extremum branch。

### 4.4 `Pre` 包含题目给出的全部单 case 保证

`Pre` 不得接收题目排除的输入。除 scalar range 和 per-element range 外，还要保留以下不能由单值范围发现的关系：

- 两个字符串不同或长度相同；
- 点、边或 key 互异；
- 题目保证解存在；
- 参数之间的大小、shape 或 consistency 关系。

测试方式是反向看输出 totality：若某个退化输入会满足当前 `Pre`，却让 `Spec` 接受 output format 禁止的输出，说明 `Pre` 少了条件。例如遗漏 `s <> t` 可能让 empty operation sequence 成为答案，而题目要求 `1 <= m`。

多 test case 的 `t` 范围、所有 test 的 `n` 总和等只约束外层 driver 的条件，不属于单次 solver call 时，不强塞进单 case `Pre`；其他题目保证不得静默丢弃。

## 5. `Require` 中范围的可见性

本节只要求 `Require` 显式展开简单输入范围，不要求 `Ensure` 展开。`Ensure` 可以直接调用完整 `Spec`，并封装 output range 与 post-state array condition。

### 5.1 每个 scalar parameter 都有显式范围

对 C signature 中每个简单输入 scalar，尤其是 `n`、`m`、`k`、row / column count 与 capacity，在 `Require` 中直接写题目给出的上下界。不要只依赖 opaque `Pre` call 或 spatial predicate。

以下事实都不能替代 scalar bound：

- `k == Zlength(cold_costs)` 只连接 scalar 与 list，不约束任何一方；
- `Int64Array::full(cold, k + 1, l)` 中的 extent 只描述资源长度，不给出题目范围；
- 某个 bound 能由其他条件推导，也不等于已经明确承载了题目保证。题目给出 `1 <= k <= K` 时仍直接写出两端。

实现自己的 overflow、representability 和 access safety 条件也直接写在 `Require`，但不得把 implementation convenience 冒充题目 domain condition 放进 `Pre`。

### 5.2 简单元素 domain 使用带有效下标 guard 的 `forall`

每个 input 或 input-output array / buffer 的元素 domain 若能清楚写成 equality 或 interval，就在 `Require` 使用显式 indexed quantification：

```c
forall i,
  0 <= i && i < logical_extent =>
  lower <= Znth(i, values, 0) && Znth(i, values, 0) <= upper
```

length equation、capacity bound 或 `TArray::full` 等 spatial predicate 本身都不表示 element range。二维对象对 row / column 都加有效 index guard，并写 applicable cell range。

若条件真正依赖位置、多个 index / array、prefix / aggregate equation 或结构关系，可以保留在完整 `Pre` 或已有业务 predicate 中，不强行改写成简单 per-element interval。例如 `partial[i + 1]`、`partial[i]` 与 `years[a - 1 + i]` 的 recurrence 不是简单元素范围。

不要为了隐藏一组简单范围再新建 `InputValid`、`InputValues`、`InputBound` 或 `SizeSafe`。直接范围与保留的完整 `Pre` 可以同时存在：前者提供 QCP contract 可见性，后者保留未展开的 cross-argument / structural 语义。无论是否在 `Require` 重述，都不得因此删除或弱化 Rocq `Pre`，用户提供的 `Pre` 继续服从 freeze 规则。

### 5.3 题目约束不能只因 `Pre` 漏写而一起消失

最终 `Pre` 与 `Require` 的语义联合必须承载题目对单次调用给出的每项保证：scalar bound、array length、per-element domain 和 cross-argument relation。不能从已有 `Pre` 反向猜约束是否完整；一个从未写入 `Pre` 的条件不会被任何展开自动恢复。

## 6. QCP contract 的语义连接

### 6.1 `Spec` 读取 pre-state 输入

即使 C 会修改或复用 input buffer，传给 `Spec` 的逻辑输入也从 pre-state contents 解码。post-state list 用于描述输出或归还资源，不能悄悄替代题目输入。

### 6.2 表示 bridge 不计算答案

contract-level bridge 只处理 representation：layout、tag、sentinel、old/new state 或 composite reconstruction。它不能包含 solver formula，也不能重述答案如何计算。这里的 representation bridge 与 assertion 中 `n == n@pre` 一类 value bridge 是不同概念。

### 6.3 domain 条件与实现条件分层

题目 domain condition 来自 `Pre`；C 实现只增加 representability、layout、ownership、index safety 和 overflow 条件。不能为了适配某个实现而把更强的 implementation-derived condition 写回数学 `Pre`。

### 6.4 每个输出都连接真实 channel

`Spec` 的每个 output component 和每个 branch 都要映射到真实 C return value 或 post-state memory。只在逻辑层出现、没有 return / post-state channel 的 output 是未连接输出。

## 7. 全局对象的 ownership

solver 读写的每个 file-scope global 都属于 memory footprint：

- `Require` 使用与 element type、concrete layout 和实际访问 extent 匹配的 spatial predicate；
- `Ensure` 归还对应 ownership；写后内容未被数学 spec 约束时，可绑定 fresh logical list；
- entry content 无关且在读取前完全覆盖的 work array 使用 `undef_*`；若 solver 依赖 entry content，使用 initialized `full`；
- extent 使用代码实际访问的表达式，并在 `Require` 保留使该 extent 安全的显式 range；
- scratch global 是实现资源，不进入题目级 `Spec`；
- function-local `static` 具有 global lifetime，也必须作为可命名、可拥有的全局资源建模。

不要遗漏只写不读的 global；写操作同样需要入口 ownership 和出口归还。

## 8. 二维逻辑对象与具体布局

题目对象本质上是 matrix、grid、table、board、image 或 row collection，且 row / column 结构能让 contract 更清楚时，使用 `list (list Z)` 或对应 nested element type，不为复用一维 predicate 而随意 flatten。

- 写 outer length、applicable row length 和 cell range；`Require` 中的简单 cell range使用 row / column guards。
- 连续 row-major C block 使用库中匹配的 `Array2Lib` typed predicate，例如签名确认后的 `IntArray2::full(p, rows, cols, matrix)`。
- `int **`、`char **` 一类 row-pointer array 使用匹配的 `PtrArray2Lib` predicate，例如签名确认后的 `IntPtrArray2::full(p, rows, matrix)` 或 `CharPtrArray2::full(p, rows, matrix)`；predicate 不含 column count 时另写 row length。
- pointer-to-pointer 不能描述成一个连续 block；连续 block 也不能描述成独立 row ownership。
- `missing_i` 等二维 operation 只有在现有库确实提供同名兼容签名时才使用。
- 只有对象本来就是一维，或完整 C interface 无法建立可靠二维 shape / layout 时才保留一维表示。

不要新造基础二维 spatial predicate。现有 predicate 无法匹配 element type 或 concrete layout 时，也不能用近似 predicate 弱化 ownership。

## 9. Predicate 可用性与签名

出现在 `Require` / `Ensure` 中的 named spatial / assertion predicate 必须来自当前 repository 已支持的接口：名称、参数类型、arity、参数顺序、predicate category 和 import / declaration 都要兼容。不要创建新的基础 memory predicate、alias、wrapper 或 representation shortcut。

`forall` / `exists`、logical connectives、equality、comparison、arithmetic 和 ordinary value-producing expression 不是新 named predicate，可以直接使用。题目级 pure predicate 仍按本 skill 的 definition hygiene 规则处理：只有题目语义或跨函数接口确实需要时，才在 active case lib 保留一层定义；不要用它包装简单范围或伪造空间 ownership。

若已有 spatial predicate 与直接逻辑语法无法忠实表达实际 layout / ownership，不得近似 contract、削弱条件或杜撰一个同名接口。
