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

## Evidence 记录

annotation handoff 必须提供能传 canonical 参数的 QCP driver。formal evidence 记录：

- driver / command 名称。
- working directory。
- target `.c` 的 round worktree 路径。
- `-I` 参数。
- `-slp` 参数。
- return code 和 diagnostic。

不能传 canonical `-I` / `-slp` 的 wrapper 不能作为 `canonical_symexec_evidence`；只能在 `qcp_mcp_interactive_evidence` 中记为 `skipped`、`failed` 或 `forbidden` 并说明原因。

generated files 只允许由 symbolic execution 刷新：`*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`。`case_lib` 不由 symbolic execution 重写。

## Reference policy

优先参考 handoff `problem_context.reference_case_hints` 指定的 case；没有 hints 时可在以下 curated 范围内主动检索相似模式：

- `QCP_demos_LLM`
- `QCP_examples/LLM_bench`
- `SeparationLogic/examples/LLM_bench`

不要参考 `QCP_demos_human`。这是 reference hygiene rule，不是 annotation candidate 的 acceptance gate。

handoff 若设置 `reference_policy.mode = deny-existing-examples`，仍以 `allowed_globs` / `denied_globs` 为准；默认允许读取 LLM bench 的 C、lib 和 generated/proof context 作为风格参考，但不得复制证明内容、不得把其他 case generated files 手工搬入当前 case。`QCP_demos_human` 和 handoff 明确 denied 的路径仍不应读取；若误读，必须如实记录并改用 allowed context 复核。

`file_access_summary` 必须是 object，记录显式 `rg`、`find`、`sed`、`cat` 等读取动作：

```json
{
  "must_log_file_reads": "yes",
  "read_categories": [],
  "searches": [],
  "denied_globs_touched": []
}
```

`file_access_summary` schema 小错误应在本次 spawn 内补正，不应停止工作。`denied_globs_touched` 是 warning / audit evidence，不是 controller hard blocker；只要 annotation-subagent 没有修改本 round allowed formal files 之外的文件，且 candidate 通过 QCP、`case_lib` check 和 annotation-checking，应继续交给 controller review。若误读 denied path，report 中记录 path、原因、后续是否用 allowed source 复核，并不得把 denied file 内容作为 acceptance evidence。

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

修复时补齐缺失的 local store、完整 `full` / `undef_full`，或补纯边界事实使数组段可合并。report 中记录原始失败行、check 行、缺失资源和最终补入的资源形态。
