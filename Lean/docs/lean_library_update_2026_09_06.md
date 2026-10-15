# Lean 库同步与 Algorithms 评估（2026-09-06）

库源码已同步，库测试及旧案例完整回归均通过。旧示例兼容修复已完成，后续 49 个 Codeforces 和 16 个 Algorithms 也已全部完成迁移，逐例结果及最终检查见[第三批报告](llm_bench_third_batch_migration.md)和[第三批清单](llm_bench_third_batch_scope.json)。

后续本地整理：NumberTheory、Prime、RelPrime、ZParity 已从示例目录移至 `auxlibs/AUXLib`，并加入 AUXLib 总入口。这是同步完成后的公共库扩展；上游同步清单仍保留同步时的原始哈希，不将本地扩展伪记为上游版本。新位置及依赖检查见[依赖清单](llm_bench_second_batch_dependencies.json)。

## 同步版本

- 目标：democases 的 PV-bench 分支，基于本地提交 3d9ab8df。本轮变更尚未提交或推送。
- 来源：本地 annotated_simplec_lean，HEAD 447a857fa2ff8307374c6100b9802c637325a5a0，加同步时的工作区修改，包括用户新加的 MaxMinLib 命名空间兼容处理及 ListLib 扩展。不能仅靠该 HEAD 复现工作区版本。
- 同步 10 个包：auxlibs、compcert_lib、fixedpoints、listlib、MonadLib、sets、unifysl、SeparationLogic，以及新加入的 flocq、maxminlib。287 个同步文件逐个记录并核对 SHA-256；源目录未作修改。
- 所有 Lean 工具链仍为 leanprover/lean4:v4.25.2。Mathlib 依赖固定为 v4.25.2，对应 c98ae54af00eaefe79c51b2b278361ca94e59bfb。
- 按 democases 的目录名改写包配置和锁文件中的相对路径。Makefile 与 PowerShell 构建入口增加 flocq、maxminlib；保留 democases 的 examples 包和案例。
- 本机只在被 Git 忽略的 .lake/packages 中复用已有依赖缓存。仓库中的包配置没有指向 annotated_simplec_lean 的绝对路径。
- 库同步阶段没有修改 C、Rocq 或既有案例。后续兼容修复仅适配 Lean 示例和检查脚本；新增案例的 C 文件只加入 Lean import/open 注释。Rocq 和 C 程序、契约保持原样。

版本记录：[同步清单](upstream_lean_sync_inventory.json)、[上游 Coq 基线](upstream_coq_source_baseline.md)、[上游兼容差异记录](upstream_migration_inconsistencies.md)。

## 验证结果

| 检查 | 结果 |
|---|---|
| MaxMinLib 与 SeparationLogic / Mathlib 联合导入 | 通过；原先 max_assoc 等全局名称冲突未再出现 |
| 新版库测试目标 | 通过（1113 个构建任务，含依赖） |
| 既有 42 个 LLM_bench 案例 VC 重生成一致性 | 通过，无 goal / goal_check 差异 |
| LLMBench + QCPDemosLLM + UpstreamLibraryChecks 构建 | 兼容修复后通过，1392 个构建任务 |
| 现有迁移审计脚本 | 通过：42 个案例，13167 个 API，3132 条源已证声明及补完的 5 条源 Admitted；2092 个继承占位不变 |

执行的库测试包括 MaxMinLibTests、ListLibTests、FlocqTests、SeparationLogicTests、SetsClassTests、P13Tests、UnifyslTests、MonadLibTests、UnifiedTacticsTests、FacadeImportTests、P12Tests，以及 AUXLib 的列表、集合重写、整数自动化、标识符映射、顺序判定和二叉树测试。UpstreamLibraryChecks 还检查两个 MaxMin 定理没有 sorryAx 依赖。

完整回归现已通过。以下保留首次同步发现的问题，均已修复；构建通过仍保留原始 Coq Admitted 基线，不表示整个仓库无占位证明。

## 已修复的兼容问题

1. Architecture32 重复声明：原有 LLM_bench/Architecture32.lean 定义的 Arch32 常量现在已在新版 CArch 中提供。minisat 和依赖检查已直接导入 SimpleC.SL.CArch，旧 Architecture32.lean 文件已删除。
2. ListLib 接口变化：list_eq_ext 变为等价式，旧脚本仍将它当作单向定理使用；increasing 的接口也发生变化。涉及 binary_indexed_tree、choosing_inns、sort_point、bucket_sort、counting_sort、quicksort 等。
3. 数组导出和名称解析：stock_trading 的 IntArray2.full 等名字落入了新版参数化接口而非原先的具体实例。案例和依赖检查均直接使用 naive_C_Rules.IntArray2 的新版具体接口；已删除 ArrayCompatibility.lean 及旧 IntArray2.undef_full 别名，依赖清单改为记录核心定义。
4. 证明脚本与自动化变化：Mathlib/新版 tactic 更早关闭部分目标，后续命令报 No goals to be solved；另有 sizeof_int 名称歧义、位运算证明目标、lcs_n 中 sep_apply 的匹配问题。
5. 旧 QCP_demos_LLM：poly_sll_lib 有重载和 Intros 匹配问题；generated/chars_goal 有 repeat_Z 导出与重载问题；bst_base_lib 有未关闭的目标。

首次构建的逐模块首个错误如下；历史完整错误列表见 [回归记录](lean_library_update_regressions.json)。

| 模块 | 首个错误 |
|---|---|
| `SimpleC.EE.LLM_bench.Engineering.minisat.vec_lib` | import SimpleC.EE.LLM_bench.Architecture32 failed, environment already contains 'SimpleC.SL.CArch.Arch32.addr_max_unsigned' from SimpleC.SL.CArch |
| `SimpleC.EE.QCP_demos_LLM.poly_sll_lib` | overloaded, errors  |
| `SimpleC.EE.QCP_demos_LLM.generated.chars_goal` | Unknown identifier `repeat_Z` |
| `SimpleC.EE.QCP_demos_LLM.bst_base_lib` | unsolved goals |
| `SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_lib` | Tactic `apply` failed: could not unify the type of `ListLib.list_eq_ext ?m.31 ?m.32 0` |
| `SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib` | No goals to be solved |
| `SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib` | Tactic `apply` failed: could not unify the type of `ListLib.list_eq_ext ?m.12 ?m.13 0` |
| `SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_lib` | Tactic `apply` failed: could not unify the type of `ListLib.list_eq_ext ?m.26 ?m.27 default_point` |
| `SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_lib` | Function expected at |
| `SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib` | Tactic `apply` failed: could not unify the type of `ListLib.list_eq_ext ?m.45 ?m.46 0` |
| `SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal` | Unknown constant `SimpleC.SL.CommonAssertion.SeparationLogicSig.IntArray2.full` |
| `SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib` | Tactic `apply` failed: could not unify the type of `ListLib.list_eq_ext ?m.30 ?m.31 0` |
| `SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib` | No goals to be solved |
| `SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib` | No goals to be solved |
| `SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_proof_manual` | sep_apply_l_atomic: the lemma's store atoms are absent from the goal premise |
| `SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_lib` | No goals to be solved |

## Algorithms：可新增范围

初始评估时，以 C 文件为计数单位，Algorithms 共 78 个；36 个已有 Lean 版本，剩余 42 个均运行了现有 mac-arm64 symexec 的 Lean VC 生成。结果为 39 个生成成功、2 个失败、1 个达到 180 秒超时。

下表保留初始评估时按共享库依赖筛选的结果。后续请求中的 16 个优先案例现已全部完成定义、库定理和 manual proof，详见[第三批报告](llm_bench_third_batch_migration.md)；其余候选仍按下述阻碍区分。

| 分类 | 数量 | 当前生成结果 |
|---|---:|---|
| 新版基础库覆盖的 MaxMin 案例 | 17 | 16 成功，streetlight 超时 |
| 需补 MonotonicList 的已用接口 | 4 | 全部成功 |
| 需补字符串规格切片（manacher） | 1 | 成功 |
| 仍需 SumLib | 3 | 全部成功 |
| 仍需图模型/相关算法库 | 16 | 15 成功，Floyd_adjacency_matrix 失败 |
| 浮点凸包 | 1 | 当前 Lean 生成后端拒绝浮点存储 |
| 未有 Lean 版本的 C 文件合计 | 42 | 39 成功、2 失败、1 超时 |

旧示例兼容问题修复后，以下 16 个新增案例已全部迁移完成。它们不需要先补完整 SumLib 或 GraphLib；部分代码中的 sum 是已有列表求和，不能据此误判为 SumLib 依赖。

### 已完成迁移的 16 个优先案例

- [coin_change](../../QCP_examples/LLM_bench/Algorithms/coin_change/coin_change.c)：61 个生成 VC 定义。
- [container_with_most_water_nlogn](../../QCP_examples/LLM_bench/Algorithms/container_with_most_water_nlogn/container_with_most_water_nlogn.c)：325 个生成 VC 定义。
- [energy_necklace](../../QCP_examples/LLM_bench/Algorithms/energy_necklace/energy_necklace.c)：131 个生成 VC 定义。
- [house_robber](../../QCP_examples/LLM_bench/Algorithms/house_robber/house_robber.c)：20 个生成 VC 定义。
- [huffman_encoding](../../QCP_examples/LLM_bench/Algorithms/huffman_encoding/huffman_encoding.c)：72 个生成 VC 定义。
- [kings_game](../../QCP_examples/LLM_bench/Algorithms/kings_game/kings_game.c)：96 个生成 VC 定义。
- [matrix_chain_multiplication](../../QCP_examples/LLM_bench/Algorithms/matrix_chain_multiplication/matrix_chain_multiplication.c)：122 个生成 VC 定义。
- [maximum_subarray](../../QCP_examples/LLM_bench/Algorithms/maximum_subarray/maximum_subarray.c)：41 个生成 VC 定义。
- [merging_stones](../../QCP_examples/LLM_bench/Algorithms/merging_stones/merging_stones.c)：122 个生成 VC 定义。
- [multiple_knapsack](../../QCP_examples/LLM_bench/Algorithms/multiple_knapsack/multiple_knapsack.c)：153 个生成 VC 定义。
- [non_overlapping_intervals](../../QCP_examples/LLM_bench/Algorithms/non_overlapping_intervals/non_overlapping_intervals.c)：76 个生成 VC 定义。
- [rmq](../../QCP_examples/LLM_bench/Algorithms/rmq/rmq.c)：206 个生成 VC 定义。
- [rod_cutting](../../QCP_examples/LLM_bench/Algorithms/rod_cutting/rod_cutting.c)：31 个生成 VC 定义。
- [split_array_largest_sum](../../QCP_examples/LLM_bench/Algorithms/split_array_largest_sum/split_array_largest_sum.c)：49 个生成 VC 定义。
- [super_piano](../../QCP_examples/LLM_bench/Algorithms/super_piano/super_piano.c)：177 个生成 VC 定义。
- [zero_one_knapsack](../../QCP_examples/LLM_bench/Algorithms/zero_one_knapsack/zero_one_knapsack.c)：66 个生成 VC 定义。

上述每例均已完成原模型、源已证辅助定理和 manual proof；继承的原 Coq Admitted 单独记录，不计入已完成证明。

### 其余候选与阻碍

- streetlight：数学模型依赖已覆盖，但现有生成器在 180 秒内未结束。保留候选资格，不能当作已通过生成，也不能据此判定不可处理。
- choir_singing、longest_increasing_subsequence、longest_nondecreasing_subsequence、max_sum_increasing_sequence：仍使用 MonotonicList（如 mono_inc）；新版尚无这部分对应接口。
- manacher：依赖 Engineering/string 与 StdLib/string_lib 中的字符串规格。新版核心 StringLib 同名谓词的字符范围与存储断言不同，需要单独补相应定义，不能直接按名称替代。
- climbing_stairs、paint_house_ii、sightseeing_bus：仍使用 SumLib 的有限枚举/集合求和等语义，单独加入 MaxMinLib 不够。
- DFS（3）、Dijkstra（2）、Floyd（3）、Kruskal（1）、Prim（4）、kosaraju（3）：共 16 个，仍需要图语义及对应算法模型。Floyd_adjacency_matrix 当前另在 C 第 160 行报无法证明指针目标可读。
- convex_hull_float：新版库提供浮点基础，但当前仓库 symexec 在 Lean 输出阶段明确报 Lean data_at does not support floating-point stores。这需要更新/扩展生成后端，单独替换 Lean 库不能解决。

逐例信息与原始生成日志路径见 [Algorithms 清单](algorithms_new_library_inventory.json)。

## 复现命令

```sh
cd Lean/examples
lake build UpstreamLibraryChecks MaxMinLibTests ListLibTests FlocqTests SeparationLogicTests
lake build LLMBench QCPDemosLLM MaxMinLibTests
cd ../..
python3 scripts/generate-llm-bench-lean.py --check
python3 scripts/check-llm-bench-lean.py --coq-lib /path/to/coq/theories
```

本轮本机完整日志：/tmp/democases-synced-library-tests.log、/tmp/democases-synced-build1.log；Algorithms 生成日志位于 /tmp/algorithms-new-library-generation/。
