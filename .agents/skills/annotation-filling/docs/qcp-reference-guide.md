# QCP、Reference 和 Resource Reclaim

本文件汇总 annotation round 中与 symbolic execution、reference policy 和 QCP resource reclaim 相关的规则。

## Include 和 symbolic execution

`QCP_examples/LLM_bench` 下复用 `QCP_demos_LLM` 公共头文件的 C case，统一使用 bare include：

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
```

symbolic execution 必须同时包含：

```bash
-IQCP_examples/QCP_demos_LLM/
-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM
```

`-I` 用于 C header search；`-slp` 用于 strategy / generated Rocq logical path。二者不能互相替代。不得为了工具调用把 bare include 改成长相对路径。

## Check 记录

annotation handoff提供完整 `controller.py symexec` command；controller code固定 driver、cwd、target和 canonical `-I`/`-slp`。成功时 report只写 `checks.symexec = passed`；失败 command/diagnostic摘要写 `agent_output.md`，不复制完整 argv/path/evidence object。

generated files 只允许由 symbolic execution 刷新：`*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`。`formal_case_lib` 不由 symbolic execution 重写。

## Reference policy

优先参考 handoff `Problem context` 中列出的 reference case hints；没有 hints 时可在以下 curated 范围内主动检索相似模式：

- `QCP_demos_LLM`
- `QCP_examples/LLM_bench`
- `SeparationLogic/examples/LLM_bench`

所有 reference 文件的只读访问都属于 allowed，包括 `QCP_demos_human`；读取、检索、比较或记录 human example 本身均不是 annotation blocker。controller 的 file-access policy 不编码“推荐 / 不推荐”等级，也不按读取路径产生 denied。文档层仍明确建议：优先参考 LLM case，允许但不推荐参考 human case。

human example 只能作为非权威思路提示。当前 candidate 仍应从当前 C、`problem_context` 和 `formal_case_lib` 推导，并通过当前 case 的 canonical QCP、`formal_case_lib` check、annotation-checking 以及后续 proof/final-check。human case 的旧 report 或通过状态不能替代这些检查。

无需把普通只读搜索逐条复制进 JSON。若某个 reference实际影响 spec设计，在 `agent_output.md` 一句话注明即可。

read-access denied 不由“读过什么文件”触发，只指当前 formal candidate 实际引入 phase contract 不允许的库、import、generated artifact 或其他 formal dependency。这类边界由 `formal_case_lib` contract、manual proof structure、group merge / parent verify 和 final-check 检查；当前 case 的 required checks 失败属于普通 verification failure，不归类为 read-access denied。

可复用模式包括只读 array scan、未初始化 buffer 逐步写入、多游标 array algorithm、C string、optimization / binary search 的可行性或最优性 spec。不要复制长相对 include、generated file 手工改动、manual helper declarations、`Admitted.`、新增 `Axiom` 或旧 report 命名。

## Reference examples

优先按数据结构和证明目标选择相似 case：

- 普通 annotation：`QCP_examples/QCP_demos_LLM/sum.c`、`sll.c`、`functional_queue.c`、`majorityElement.c`。
- refinement / safeExec annotation：`QCP_examples/QCP_demos_LLM/sll_merge_rel.c`、`kmp_rel.c`、`int_array_merge_rel.c`。
- branch-control：`QCP_examples/QCP_demos_LLM/bubble_sort.c`、`QCP_examples/QCP_demos_tutorial/branch_destruct.c`、`branch_join_private_condition.c`、`multiinv_examples.c`。
- 二分答案 / 可行性 predicate：`.agents/skills/annotation-filling/docs/correct-examples/split_array_largest_sum/split_array_largest_sum.c` 和同目录的 `binary-search-annotation.md`。

参考这些 case 时，学的是隐藏性质、路径命名、array predicate 选型和数学 spec 表达方式，不复制 generated files、manual proof bodies、helper declarations 或旧 formal 文件边界。

## Resource reclaim 错误

QCP 在 `return`、函数尾或 local scope 结束处报 `remove permission failed`，通常是 annotation 缺少 live local resource。

常见原因：

- full assertion 丢掉 live local 的 `store_*(&x, v)`。
- 局部数组只保留已写前缀，离开 scope 前没有合回完整数组。
- 未初始化数组被拆成碎片，函数结束前没有完整 `undef_full` 或 `full`。
- 使用 `by local` 后误以为它保留空间资源。
- 为补权限额外叠加裸 permission，和已有 local store 重复或不匹配。

排查方式：

1. 使用独立 qcp-mcp 会话检查失败点上一句的 symbolic state。
2. 若整体 symbolic execution 在 `return` 行失败，先对 `return` 上一行执行 check。
3. 确认 state 中包含当前 scope 的所有 live local store。
4. 对局部数组，确认 state 中是完整数组资源，或策略能在该点合回完整资源。

例如 `int a[2003];` 在 `return` 前通常应能看到 `IntArray::undef_full(a, 2003)` 或 `IntArray::full(a, 2003, l)`，而不是只留下无法回收的 prefix/suffix fragments。

修复时补齐缺失的 local store、完整 `full` / `undef_full`，或补纯边界事实使数组段可合并。需要复用时在 `agent_output.md` 记录失败点、缺失资源和最终资源形态。
