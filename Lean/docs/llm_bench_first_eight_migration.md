# LLM_bench 首批八个案例迁移

这批迁移覆盖下表八个案例的完整 VC、自动证明文件、手动证明文件、检查入口和案例库。Coq 已完成的 174 条 `Qed` 均有通过 Lean 内核检查的证明；原有 145 条 `Admitted` 中，`optimized_selection_sort` 的 5 条 manual 已补成完整 Lean 证明。八个案例共 132 条 manual 证明均无 `sorry`，剩余 140 条空缺全部位于自动证明文件，仍明确保留其 Coq 来源。

## 来源与范围

- 仓库基线：`qcp-binary-democases`，提交 `e95ad5cea97c21f90e12a7434ccb65a06e53254c`。
- 子模块基线：`mcp/rocq-mcp` 固定于 `674f21a5aed9604359741c4d51dd5096f4cc8cec`，迁移时未初始化；本批读取仓库内 `Rocq/` 的源码。
- Lean 工具链：`leanprover/lean4:v4.25.2`。
- [逐声明清单](llm_bench_first_eight_inventory.json)记录 39 个案例源文件的 SHA-256、Coq 声明、Lean 对应名称、原始证明状态，以及另外使用的依赖片段。此处基线独立于既有基础库迁移的 `annotated_simplec` 基线。

| 案例 | 已迁移的原有 Qed | 已补证的原有 Admitted | 仍保留的 Admitted |
| --- | ---: | ---: | ---: |
| selection_sort | 15 | 0 | 13 |
| modular_inverse | 2 | 0 | 5 |
| optimized_selection_sort | 0 | 5 | 17 |
| bubble_sort | 29 | 0 | 23 |
| insertion_sort | 21 | 0 | 19 |
| modular_mul | 60 | 0 | 36 |
| modular_power | 29 | 0 | 15 |
| linear_modular_inverse | 18 | 0 | 12 |
| 合计 | 174 | 5 | 140 |

计数包含案例库与证明文件，同名共享定理按其各自的 Coq 声明计数。`optimized_selection_sort` 的原有 22 条空缺中，5 条手动证明现已完成，17 条自动证明仍保留。该文件另外 12 个以 `Abort` 结束的试验不产生 Coq 声明，清单明确排除，Lean 也不为其引入假设。

补齐的五条 manual 分别证明初始化、内层循环初始化、交换最小值后的不变量、无需交换时的不变量，以及退出循环后的完整有序性。交换分支逐位置检查 `Znth`，保持排列关系并将有序前缀推进一格；退出分支覆盖前缀已占满数组或只剩最后一个元素两种情况。原始 C、VC 定义和 Coq 源文件未修改；清单分别保存原始 `coq_proof` 与新增的 `lean_proof: proved` 状态。

## 目录与接口

每个案例位于 `Lean/examples/SimpleC/EE/LLM_bench/Algorithms/<case>/`，五个文件同级：

```text
<case>_lib.lean
<case>_goal.lean
<case>_proof_auto.lean
<case>_proof_manual.lean
<case>_goal_check.lean
```

`goal` 和 `goal_check` 由仓库的 `symexec` 从原 C 注解生成。八个 C 文件各新增一条案例库的 `Import Lean`，算法和契约未修改。`goal_check` 构造 `VC_Correctness : VC_Correct`，逐字段连接完整证明集合；Coq `Module Type` 内的 `Axiom` 对应 Lean 结构体字段，不是新的全局公理。

公共的排序定义和证明放在 `Lean/auxlibs/AUXLib/Sorting.lean`，案例库通过 `export` 保留各自名称。这里使用当前 Coq `ListLib.v` 的递归 `increasing_aux`、`increasing`、`lowerbound`、`strict_lowerbound`，避免把案例无声地绑定到既有 Lean 基础库的另一种定义表示。`insert` 与 `last_val_local` 保留案例源文件的递归行为。算术辅助证明放在 `Lean/auxlibs/AUXLib/Arithmetic.lean`，保持 `Z.div`/`Z.modulo` 的向下取整语义，以及 `Z.quot`/`Z.rem` 的向零截断语义。

Coq 的 `selection_sort` 没有自己的 `_lib.v`；Lean 补上同级库文件，提供它实际依赖的 `QCP_demos_LLM/bubble_sort_lib.v` 三条定理：`increasing_sublist_elim`、`increasing_sublist_intro`、`permutation_swap_Znth_lt`。这三条也全部有证明，但不计入上表的 174 条案例源 `Qed`，不声称迁移了该依赖文件的全部声明。

证明使用已有 Lean 分离逻辑策略，包括 `pre_process`、`aggressive_pre_process`、`Exists`、`sep_apply`、`split_pure_spatial` 和 `cancel`。部分复合 VC 选取生成目标本身的纯逻辑右分支，再显式组合子目标定理。证明步骤允许适应 Lean；本批不宣称 `LLM_pre_process` 或 `Goal_apply` 与 Coq Ltac 的全部搜索行为一致，也没有增加只在单个定理中生效的同名策略替身。公开表示差异记录于 [迁移差异表](migration_inconsistencies.md#llm_bench-first-eight-cases)。

## 生成与验证

在仓库根目录执行：

```sh
python3 scripts/generate-llm-bench-lean.py --check selection_sort modular_inverse optimized_selection_sort bubble_sort insertion_sort modular_mul modular_power linear_modular_inverse
python3 scripts/check-llm-bench-lean.py
(cd Lean/examples && lake build LLMBench)
```

`Lean/Makefile` 还提供检查所有已登记案例的入口；登记后续批次后，此命令也会检查后续批次。本报告的首八个案例可以用上面的显式范围独立验证：

```sh
make -C Lean llm-bench-check
```

需要同步修改后的 C 注解时，执行 `python3 scripts/generate-llm-bench-lean.py`，也可在末尾指定一个或多个案例名。该脚本在临时目录生成，只有 `goal` 和 `goal_check` 会写回；案例库、自动证明和手动证明始终保留，随后通过构建发现不再适用的证明。`--check` 比较生成结果，不写文件。可用 `--symexec /path/to/symexec` 指定其他二进制。

`LLMBench` 已接入仓库根目录和 `Lean/examples` 两处 Lake 配置，须显式指定该目标。首批案例通过各自的 `goal_check` 连接并检查证明。首批额外的聚合 API、公理依赖及行为检查文件已按要求删除；上文证明计数和公理审计结果记录的是当时的验收结果。Python 检查继续核对源文件哈希，以及 140 处剩余空缺的精确声明集合，拒绝新增 `axiom`、`unsafe`、`admit` 或额外 `sorry`。

迁移验证通过：重新生成比对、原始空缺集合核对、完整 `LLMBench` 构建及全部 179 条已完成声明的 `sorryAx` 依赖审计。构建出现对应原有 `Admitted` 的 `declaration uses 'sorry'` 警告属于记录的基线，不能据此将这些声明算作已完成证明。
