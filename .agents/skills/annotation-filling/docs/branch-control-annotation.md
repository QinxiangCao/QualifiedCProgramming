# Branch Control Annotation 指南

本文说明 annotation-subagent 在填写 annotation 时，如何使用 branch-control 特性管理符号执行中的多分支状态。本文件同时给出当前 branch-control 语法约定和 annotation 实践规则，作为本仓库内可独立使用的说明。

## 何时使用 branch control

当 C 程序有以下形态时，优先考虑 branch control，而不是用一个巨大 `Assert` / `Inv Assert` 强行吞掉所有情况：

- 分支后每条路径保留不同纯事实，例如 `x == 0` / `x > 0`。
- 循环入口有不同阶段或边界情况，例如 `n == 0` 和 `n > 0`。
- 某些路径已经不可能，需要显式清除。
- 多条路径在后续语义相同，需要显式合并。
- 需要对某一组 branch 做分类讨论，但不想影响其他 branch。

核心原则是：先给语义不同的路径命名，再只对目标 branch 做局部 assertion / invariant 转换；只有路径语义真正汇合时才 join。

## Branch 名称

`Branch name` 用条件给当前 branch 命名：

```c
/*@ Branch name
    zero: x == 0;
    positive: x > 0
*/
```

如果当前位置只有一个 branch，可以用简写：

```c
/*@ Branch name entry */
```

使用规则：

- `all` 和 `unnamed` 是保留名，不能作为普通名字。
- 命名会覆盖旧名字。
- 一个名字可以对应多个 branch。
- 已命名 branch 后续自然分裂时，新 branch 继承原名字。
- 如果某个名字的条件匹配不到任何 branch，工具会报错；不要用不确定条件试探命名。

## `$ branch_list` 指令

很多 annotation 可用 `$ branch_list` 选择作用范围：

```c
/*@ Assert x >= 0 $ zero positive */
/*@ x >= INT_MIN by local $ normal */
```

使用规则：

- 写了 `$ branch_list` 时，只转换被选中的 branch，未选中的 branch 保持不变。
- 不写 `$ branch_list` 时等价于 `$ all`。
- `all` 选择当前所有 branch，`unnamed` 选择未命名 branch。
- `$` 不用于普通 `Inv` 的 case 选择；循环 case 选择使用 multi-inv 的 case/direct 机制。

当某条局部事实只在一个阶段成立时，应把 `$` 写出来，避免把事实错误地要求到其他 branch 上。

## Assert 的分组语义

当前版本中，未带 `$` 的 `Assert` 不会把所有 branch 无差别合并，而是按当前 branch name 分组：

```c
/*@ Branch name zero: x == 0; one: x == 1 */
/*@ Assert x >= 0 */
```

这里 `zero` 组和 `one` 组分别检查并替换为 `x >= 0`，结果仍保留各自名字。unnamed branch 单独组成 unnamed 组。

如果 `Assert` 本身是 branching assertion，例如 `P || Q`，则每个名字组都会分别分裂成 `P` / `Q` 两个结果 branch，并继承该组名字。

写 annotation 时可以利用这个行为保留 case 信息；如果你真正想把多个名字的 branch 合成一个状态，应显式使用 `Branch join`。

## Destruct 析构

`Destruct` 用来对选中的 branch 做分类讨论：

```c
/*@ Destruct $ all with
    zero: n == 0;
    normal: n > 0
*/
```

当选择了多个源 branch 时，每个 destruct case 必须给每个源 branch 都提供一个新名字：

```c
/*@ Destruct $ zero one with
    zero_low one_low: x < 10;
    zero_high one_high: x >= 10
*/
```

工具会为每个源 branch 生成覆盖性检查：原 assertion 需要推出所有 destruct 条件的析取。不要把 `Destruct` 当作无证明代价的 case split；条件必须由当前 branch 语义覆盖。

参考：

- `QCP_examples/QCP_demos_tutorial/branch_destruct.c`
- `QCP_examples/QCP_demos_LLM/bubble_sort.c`

`bubble_sort.c` 先用 `Destruct $ all` 把 `n == 0` 与 `n > 0` 分成 `zero` / `normal`，再分别给外层循环写 case invariant。这样零长度数组 case 不需要承担 `1 <= n`、`0 <= i <= n - 1` 等只对 normal case 成立的事实。

## Branch 清理

`Branch clear` 删除指定的不可能 branch：

```c
/*@ Branch clear zero */
/*@ Branch clear unnamed */
/*@ Branch clear all */
```

使用规则：

- 工具会检查被清除 branch 的 assertion 是否蕴含矛盾。
- 能自动证明时直接删除，不能自动证明时生成 proof obligation。
- 选择列表没有匹配到 branch 时当前会给 warning。

常见用法是在 multi-inv 或 if/else 后删除已经不可能继续执行的阶段。不要用 `Branch clear` 掩盖真实可达路径；如果清不掉，应回头检查前置条件、分支条件或命名是否正确。

参考：

- `QCP_examples/QCP_demos_tutorial/multiinv_examples.c`

## Branch 合并

`Branch join` 合并指定 branch：

```c
/*@ Branch join zero one into both with x >= 0 */
/*@ Branch join zero one into both with Assert x == 0 || x == 1 */
```

当 `with` 后面是 partial assertion 时：

- 工具对每个被选中 branch 做 partial solve。
- 被合并 branch 的 frame 必须能对齐。
- 结果必须是非 branching 的单 branch。
- 写了 `into both` 时结果名为 `both`，否则为 unnamed。

当 `with` 后面是 full `Assert` 时：

- join 结果直接等于 `Assert` 写出的内容。
- `Assert` 可以是 branching assertion，例如 `P || Q`。
- 写了 `into both` 时，`Assert` 产生的所有结果 branch 都命名为 `both`。
- 未选中的 branch 保持不变。

当 if/else 两边执行不同赋值但之后只需要一个共同抽象事实时，优先用 `Branch join` 提炼该事实。例：

```c
/*@ Branch join all with x == step(x@pre) */
```

参考：

- `QCP_examples/QCP_demos_tutorial/branch_join_private_condition.c`

## Inv Assert 和普通 Inv

`Inv Assert` 是 full invariant，语义与 `Assert` 的 branch name 分组一致：

```c
/*@ Branch name zero: x == 0; one: x == 1 */
/*@ Inv Assert x >= 0 */
while (x >= 0) {
  ...
}
```

普通 `Inv` 是 partial invariant；它会为每个 case partial solve 出 frame，并在后续再次到达同一 case 时复用已求出的 full invariant。

multi-inv 用 case name 表示循环阶段：

```c
/*@ Inv
    zero:
      n == 0 && inv_zero;
    normal:
      n > 0 && inv_normal
    with
    zero ==> zero
    normal ==> normal
*/
while (...) {
  ...
  /*@ normal ==> normal */
}
```

使用规则：

- 若没有显式 direct target，命名 branch 默认尝试进入同名 inv case。
- 显式 `pre ==> case` 会覆盖默认匹配。
- 多个 branch 进入同一 case 时，相当于先按该 case invariant 做 join/solve。
- 可能进入循环但找不到 inv case 的 branch 会报错。
- 明确不会进入循环的 branch 可自然流向循环之后，不要求有 inv case。
- 同一个 branch 被显式定向到多个不同 case 会报错。

参考：

- `QCP_examples/QCP_demos_tutorial/multiinv_examples.c`
- `QCP_examples/QCP_demos_LLM/bubble_sort.c`

`bubble_sort.c` 展示了两种写法：一种显式写 `with zero ==> zero; normal ==> normal`，另一种依赖命名 branch 默认进入同名 case。写新 annotation 时，如果 case 关系容易被误读，优先显式写 `with` 映射。

## which implies 中的 branch 名

`which implies` 支持输入和输出 branch 名：

```c
/*@ pre $ a b
    which implies
    post $ a1 a2 b1 b2
*/
```

如果每个输入 branch 分裂成多个输出 branch，输出名字按产生顺序对应新 branch。使用时要保证输出名字数量与实际分裂数量一致，并在 report 中说明名字如何对应语义路径。

## 选择策略

- 要保留路径差异：用 `Branch name` 或 `Destruct`。
- 只想在某些路径上补事实：用 `$ branch_list`。
- 要删除不可能路径：用 `Branch clear`，并确认矛盾是语义上真实的。
- 要把多条路径变成共同事实：用 `Branch join`。
- 循环有阶段或边界情况：用命名 branch + multi-inv case，必要时显式 `==>`。
- 只是想写完整循环状态且所有 branch 同构：用 `Inv Assert`，但仍要记住它按 branch name 分组。

## 常见错误

- 把 `all` / `unnamed` 当普通名字。
- 忘记 `$ branch_list`，导致局部事实被要求到所有 branch。
- 误以为 unnamed `Assert` 会合并所有 branch；当前版本按 branch name 分组。
- 用 partial assertion `Branch join` 产生 branching assertion；需要 branching 结果时使用 `with Assert ...`。
- `Destruct` 选择多个源 branch，却每个 case 只给一个新名字。
- 循环入口已命名，但 multi-inv case 名不匹配，也没有显式 `with pre ==> case`。
- 用 `Branch clear` 删除其实可达的路径，导致后续 VC 变成 annotation-bug。

## Notes 要求

如果本轮 annotation 使用了 branch control，在 `agent_output.md` 简要说明：

- 使用了哪些 branch 名，它们分别代表什么语义路径。
- 哪些 annotation 使用了 `$ branch_list`，为什么只作用于这些 branch。
- 是否使用 `Destruct`、`Branch clear` 或 `Branch join`，以及它们对应的覆盖性、矛盾性或共同事实。
- 循环 multi-inv 的 case/direct 映射，特别是哪些 branch 默认进入同名 case，哪些用了显式 `==>`。
- 这些 branch-control 决策是否可能影响 witness 结构或后续 manual VC。
