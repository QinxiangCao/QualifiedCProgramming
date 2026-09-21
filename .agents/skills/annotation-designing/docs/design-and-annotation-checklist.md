# Annotation 自检清单

本清单用于核对[知识规则](spec-and-contract-knowledge.md)中的产物要求，不增加 workflow 阶段或报告字段。

## Spec

- 已先写 Signature、Preconditions 和 Output。
- Spec 只来自题意、输入输出格式和消除歧义所需的样例说明。
- Output 唯一时使用 functional 形式；允许多个答案时使用 relational 形式。
- 自然语言 Output、Rocq Spec 与 C Ensure 同义。
- 换一份合理实现后 spec 仍成立。
- 顶层 spec 不包含当前循环、DP 转移、scratch table 构造或算法执行器。
- 题目隐含对象在 Spec 中直接量化。
- Pre 保留题目输入保证；结果 predicate 不混入输入限制和实现安全条件，但保留合法候选集合、量化有效域、答案区间与输出格式。
- 新 spec、helper 和 annotation 的逻辑整数、长度、下标统一使用 Z、Zlength、Znth、sublist、replace_Znth，没有新增 nat / length / nth 表示。

## Predicate

- 写新 definition 前已经搜索当前 dependency、canonical case lib 和公共库。
- list、Forall、Permutation、单调性、sum、最值、路径和数组资源复用已有接口。
- 最值使用 MaxMinLib 的 min_value_of_subset / max_value_of_subset，没有自定义 IsMinimum / IsMaximum；必要的 case predicate 直接复用库语义，空候选分支符合题意。
- 求和与枚举使用 sum_range / sum / sum_set_R、Zrange，没有重复递归定义；已确认 import、参数类型、Finite 和闭区间/半开区间端点。
- Relation 的零步或多步闭包使用当前依赖的 clos_refl_trans，没有同义递归 Reachable / 执行链，也未用有限次 composition 替代闭包。
- 与下标无关的逐元素性质使用 Forall，片段性质写在对应 sublist 上；两表对应关系使用 Forall2，真正依赖位置的条件保留有效下标 guard。
- Znth 可能遇到负下标时已有符合题意的 guard 或有效域；未把负下标误作通用 default，已区分非空列表首元素与空列表 default。
- 一个 case 的同类性质只使用一套已有 predicate。
- 没有 In、范围、等式或输入条件的同义包装。
- 核心 predicate 的组合直接使用，没有逐层嵌套的同义 wrapper。
- 题目或跨函数接口需要名称时只保留一层 case predicate，其他 predicate 直接引用它。
- 每个新 predicate 都表示明确数学性质，名称说明题目或接口，或替代重复公式，且参数最小。
- 同一性质在 spec、helper 和 invariant 中引用同一个定义。
- 结果、helper、进度 pure predicate 及 Record 不混入空间 ownership、输入范围集合或实现安全条件；没有用另一种名称隐藏范围包装。

## Function spec

- With、Require 和 Ensure 的逻辑值与资源对应。
- 输入范围、元素范围、overflow 和执行安全条件直接展开。
- Require 含入口资源，Ensure 归还资源。
- 顶层函数直接连接题目 Spec。
- Ensure 的数学部分只承诺所需最终性质，没有复制输入范围、循环控制状态、安全条件或中间构造过程；必要资源单独归还。
- Helper 只承诺 caller 使用的抽象结果。
- Workspace 内容只有在 caller 依赖时才成为对外数学承诺。

## Loop invariant

- 每个 lexical loop 有一条 Inv Assert。
- Plan 为每个循环写了一句数学进度。
- Invariant 只含进度、下一步需要的范围、live resources、必要读取绑定与 @pre bridge。
- Invariant 可以初始化、保持，并在退出时连接下一阶段或 Ensure。
- 函数入口条件没有整段复制到每个循环。
- 后续需要的范围直接写在 annotation，未塞入进度 predicate，并与 Spec 的语义边界及 Forall 规则一致。
- 数组资源已给出的长度和区间事实没有重复。
- @pre bridge 只用于未改变变量，之后统一使用当前变量名。
- 普通 Assert 只补 symbolic execution 无法确定且下游需要的状态。
- return 和 Inv Assert 前没有普通 Assert。

## Plan 与 retry

- function_specs 对每个 C function spec 只有一句含义。
- loop_invariants 对每个循环只有一句进度。
- new_predicates 只列当前 case 实际新增的 predicate，并说明核心接口为何不足。
- Plan 不复制完整 invariant、资源或 case-lib definition。
- 首次 attempt 的 vc_comparisons 为空。
- Retry 直接比较 old manual 与 current manual 的命题内容。
- 每项只记录 VC、annotation location、old gap、change 和 result。
- result 为 unresolved 时继续当前 attempt；全部 resolved 后再设 ready。

## 完成

- formal-case-lib-design 通过。
- symexec 通过。
- active formal_case_lib 的检查通过。
- generated files 只由 symexec 更新。
- proof manual 未手改，proof 未写入 annotation attempt。
- agent_report.json 成功时只有 status: completed。
