# 第三批 LLM_bench Lean 迁移

> 2026-10-13 目录整理：本文中的审计及历史兼容记录描述当时的验证结果。独立的 `*_proof_audit.lean`、`*_proof_historical.lean`、`*_historical_goals.lean` 和 `*_vc_compat.lean` 已移除；当前证明需要的辅助引理归入对应 lib 或 manual/partN，未使用的旧证明已删除。`proof_helpers`、`length_proofs`、`array_views` 的内容已合入对应 lib。

按后续要求，已删除 `DependencyChecks.lean`、`SecondBatchChecks.lean`、`SecondBatchSemantics.lean`、`SecondBatchBehaviorChecks.lean`、`ThirdBatchChecks.lean` 五个聚合或回归测试文件。LLM_bench 总入口直接导入 107 个案例的 goal_check。下文相关 API、公理及行为检查数字保留为历史验收记录；当前 Python 检查脚本检查源码哈希、清单状态与显式证明空缺集合，不再运行已删除的聚合检查。

65 个新案例全部完成。 本批范围固定为 shard00/shard09 的 49 个 Codeforces 案例和 Algorithms 的 16 个案例；加上前两批 42 个，完整回归范围为 107 个。

后续目录整理：共用数学接口 NumberTheory、Prime、RelPrime、ZParity 已移至 `Lean/auxlibs/AUXLib`，旧示例路径已删除，调用方直接使用 `AUXLib.*`。下文的联合验收及同步哈希统计记录第三批完成时的状态；AUXLib 总入口随后增加的本地导出单独记录，不改写上游同步快照。

## 库版本与旧例兼容

以 `PV-bench` 分支 `3d9ab8dfd327d832d4e6141d2629517d0fccb3e6` 为工作区基线。新版库来自本地 `annotated_simplec_lean` 的 `447a857fa2ff8307374c6100b9802c637325a5a0` 加用户当时的工作区修改，含 MaxMin 和 ListLib 兼容处理。287 个同步文件有逐文件 SHA-256 清单，不能仅用上游提交号替代该清单。工具链为 Lean 4.25.2 / Mathlib 4.25.2。

旧例已修复 Arch32 重复导出、ListLib 等价式接口、具体数组实例的名称解析、sizeof 歧义及 tactic 提前关闭目标后的命令等问题。修复涉及 lib、manual、生成规范化及检查入口，并非只改 manual。完整说明见 [库同步与兼容报告](lean_library_update_2026_09_06.md) 和 [同步哈希清单](upstream_lean_sync_inventory.json)。

## 文件和证明范围

- 每例有对应的 lib、goal、proof_manual、proof_auto、goal_check；Codeforces 仍按 shard 同级布局。大型 lib 可通过同名入口导入分层证明模块。
- C 文件仅增加文件级 Lean import/open 注释；程序、契约及原有注释的字节内容受哈希检查保护。Rocq/examples/LLM_bench 相对 HEAD 无修改。
- 本批生成了 6324 个 VC 定义。手工证明由 subagent 逐例完成；库定理保留源模型、公开名称、原前提和结论。
- 本批源文件含 5330 条 Qed 和 7 条 Defined。已完成案例的这些声明均纳入 Lean.collectAxioms 递归检查，禁止 sorryAx；Coq Module 别名也逐成员检查透明转发关系。
- 本批 2940 条原 Coq Admitted 显式保留在对应 auto 中，名称集合严格核对；它们不计入已完成证明。前两批仍有 2092 条继承占位，另有此前已经补完的 5 条源 Admitted。
- C 内存布局的既有 sizeof 等参数与逻辑公理属于共享验证模型；逐例审计不将它们误称为新增数学定理。新增库证明使用标准逻辑公理，未新增数学公理。

`Pinkie Pie` 的源 `Spec` 是完整频率表导出的闭式公式，`ArrangementSpec` 是独立定义。本次保留二者原样，不声称已经补出 Coq 本身未提供的二者等价证明。类似地，迁移通过只说明源规格及源已证义务的覆盖，不自动加强源规格。

## 检查与复现

`generate-llm-bench-lean.py --check` 在临时目录重生成并对比 goal/goal_check；`check-llm-bench-lean.py` 核对源码哈希、迁移清单状态和严格 Admitted 名称集合。后者默认拒绝未完成案例，`--completed-only` 仅用于迁移期间的进度检查。

```sh
cd Lean/examples
lake build LLMBench QCPDemosLLM UpstreamLibraryChecks
cd ../..
python3 scripts/generate-llm-bench-lean.py --check
python3 scripts/check-llm-bench-lean.py --coq-lib /path/to/coq/theories
```

状态与完整源接口清单：[scope](llm_bench_third_batch_scope.json)、[inventory](llm_bench_third_batch_inventory.json)。最终联合检查证据在 scope 的 final_validation 字段中记录；逐例 `_proof_audit.lean` 在当时用于检查，现已移除；原聚合审计文件已删除。

独立源码复核逐项检查了 Logo Turtle 和 Character Swap 的 30 个模型、70 条源 Qed，并核对 Pinkie 的规格边界；未发现需修复偏差。见[复核报告](third_batch_review/review.md)。该复核是人工源码接口检查，不是机械化跨语言等价证明。

## 最终联合验收

| 检查 | 结果 |
|---|---|
| 新增迁移 | 65/65：shard00 20 个、shard09 29 个、Algorithms 16 个 |
| 完整构建 | LLMBench + QCPDemosLLM + UpstreamLibraryChecks 通过；2049 个任务（含依赖） |
| VC 重生成 | 107 个案例、214 个 goal/goal_check 文件，差异为 0 |
| 公开接口与已证声明 | 33205 个 API；8469 条源 Qed/Defined 与此前补完的 5 条源 Admitted 覆盖检查通过 |
| 原 Coq 占位 | 总计 5032 条，其中本批 2940 条；严格核对名称集合 |
| 同步版本与源文件 | 287 个库文件哈希一致；Coq 无修改；65 个 C 文件剥离新增 Lean 注释后与原始哈希一致 |

全量审计最初触发 Lean 解释器对过大声明数组的递归限制，现将递归公理检查调整为每组 50 条，全部 5337 条本批源已证声明仍参与检查。最终构建已通过。

## 逐例清单

| 类别 | 案例 | VC 定义 | 源 Qed / Defined | 继承 Admitted | 状态 |
|---|---|---:|---:|---:|---|
| shard00 | [P003_1763A_absolute_maximization](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P003_1763A_absolute_maximization.c) | 19 | 31 | 8 | 完成 |
| shard00 | [P004_1890A_doremys_paint_3](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P004_1890A_doremys_paint_3.c) | 54 | 55 | 20 | 完成 |
| shard00 | [P006_38A_army](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P006_38A_army.c) | 15 | 13 | 3 | 完成 |
| shard00 | [P008_1537B_bad_boy](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P008_1537B_bad_boy.c) | 11 | 3 | 10 | 完成 |
| shard00 | [P009_1696B_nit_destroys_the_universe](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P009_1696B_nit_destroys_the_universe.c) | 35 | 34 | 22 | 完成 |
| shard00 | [P011_765A_neverending_competitions](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P011_765A_neverending_competitions.c) | 6 | 5 | 2 | 完成 |
| shard00 | [P012_1326A_bad_ugly_numbers](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P012_1326A_bad_ugly_numbers.c) | 18 | 19 | 12 | 完成 |
| shard00 | [P013_1744C_traffic_light](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P013_1744C_traffic_light.c) | 91 | 59 | 47 | 完成 |
| shard00 | [P014_1784A_monsters_easy_version](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P014_1784A_monsters_easy_version.c) | 29 | 18 | 17 | 完成 |
| shard00 | [P021_2030C_a_true_battle](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P021_2030C_a_true_battle.c) | 39 | 19 | 22 | 完成 |
| shard00 | [P023_765B_code_obfuscation](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P023_765B_code_obfuscation.c) | 28 | 24 | 12 | 完成 |
| shard00 | [P024_1104B_game_with_string](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P024_1104B_game_with_string.c) | 36 | 44 | 20 | 完成 |
| shard00 | [P026_1355A_sequence_with_digits](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P026_1355A_sequence_with_digits.c) | 44 | 44 | 13 | 完成 |
| shard00 | [P030_1113B_sasha_and_magnetic_machines](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P030_1113B_sasha_and_magnetic_machines.c) | 64 | 70 | 20 | 完成 |
| shard00 | [P035_807B_t_shirt_hunt](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P035_807B_t_shirt_hunt.c) | 67 | 48 | 33 | 完成 |
| shard00 | [P040_1983C_have_your_cake_and_eat_it_too](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P040_1983C_have_your_cake_and_eat_it_too.c) | 174 | 102 | 88 | 完成 |
| shard00 | [P047_1523C_compression_and_expansion](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P047_1523C_compression_and_expansion.c) | 37 | 35 | 23 | 完成 |
| shard00 | [P048_1771C_hossam_and_trainees](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P048_1771C_hossam_and_trainees.c) | 153 | 170 | 60 | 完成 |
| shard00 | [P053_1393C_pinkie_pie_eats_patty_cakes](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P053_1393C_pinkie_pie_eats_patty_cakes.c) | 56 | 43 | 26 | 完成 |
| shard00 | [P058_132C_logo_turtle](../../QCP_examples/LLM_bench/Codeforces/examples_shard00/P058_132C_logo_turtle.c) | 303 | 163 | 174 | 完成 |
| shard09 | [P002_1382A_common_subsequence](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P002_1382A_common_subsequence.c) | 33 | 16 | 16 | 完成 |
| shard09 | [P003_1438A_specific_tastes_of_andre](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P003_1438A_specific_tastes_of_andre.c) | 10 | 6 | 4 | 完成 |
| shard09 | [P004_2008B_square_or_not](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P004_2008B_square_or_not.c) | 90 | 34 | 56 | 完成 |
| shard09 | [P005_707A_brains_photos](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P005_707A_brains_photos.c) | 23 | 14 | 14 | 完成 |
| shard09 | [P011_460A_vasya_and_socks](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P011_460A_vasya_and_socks.c) | 18 | 11 | 7 | 完成 |
| shard09 | [P012_1139B_chocolates](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P012_1139B_chocolates.c) | 41 | 23 | 26 | 完成 |
| shard09 | [P014_1765E_exchange](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P014_1765E_exchange.c) | 9 | 15 | 5 | 完成 |
| shard09 | [P017_753A_santa_claus_and_candies](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P017_753A_santa_claus_and_candies.c) | 31 | 25 | 17 | 完成 |
| shard09 | [P018_1382B_sequential_nim](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P018_1382B_sequential_nim.c) | 22 | 15 | 11 | 完成 |
| shard09 | [P020_433A_kitahara_harukis_gift](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P020_433A_kitahara_harukis_gift.c) | 82 | 79 | 30 | 完成 |
| shard09 | [P021_602A_two_bases](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P021_602A_two_bases.c) | 36 | 29 | 9 | 完成 |
| shard09 | [P022_705B_spider_man](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P022_705B_spider_man.c) | 29 | 45 | 14 | 完成 |
| shard09 | [P027_459A_pashmak_and_garden](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P027_459A_pashmak_and_garden.c) | 63 | 26 | 44 | 完成 |
| shard09 | [P029_817A_treasure_hunt](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P029_817A_treasure_hunt.c) | 32 | 16 | 16 | 完成 |
| shard09 | [P030_1220C_substring_game_in_the_lesson](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P030_1220C_substring_game_in_the_lesson.c) | 28 | 31 | 14 | 完成 |
| shard09 | [P039_435B_pasha_maximizes](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P039_435B_pasha_maximizes.c) | 30 | 84 | 20 | 完成 |
| shard09 | [P040_81A_plug_in](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P040_81A_plug_in.c) | 31 | 20 | 19 | 完成 |
| shard09 | [P044_837C_two_seals](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P044_837C_two_seals.c) | 195 | 116 | 84 | 完成 |
| shard09 | [P046_1243B2_character_swap](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P046_1243B2_character_swap.c) | 112 | 67 | 76 | 完成 |
| shard09 | [P047_1582D_vupsen_pupsen_and_0](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P047_1582D_vupsen_pupsen_and_0.c) | 131 | 60 | 74 | 完成 |
| shard09 | [P048_1607E_robot_on_the_board_1](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P048_1607E_robot_on_the_board_1.c) | 176 | 148 | 47 | 完成 |
| shard09 | [P053_1594D_the_number_of_imposters](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P053_1594D_the_number_of_imposters.c) | 155 | 134 | 89 | 完成 |
| shard09 | [P055_276D_little_girl_and_maximum_xor](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P055_276D_little_girl_and_maximum_xor.c) | 23 | 18 | 10 | 完成 |
| shard09 | [P066_1288D_minimax_problem](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P066_1288D_minimax_problem.c) | 155 | 115 | 64 | 完成 |
| shard09 | [P073_1799D2_hot_start_up](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P073_1799D2_hot_start_up.c) | 180 | 172 | 54 | 完成 |
| shard09 | [P075_1474D_cleaning](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P075_1474D_cleaning.c) | 125 | 89 / 7 | 75 | 完成 |
| shard09 | [P081_432E_square_tiling](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P081_432E_square_tiling.c) | 518 | 344 | 274 | 完成 |
| shard09 | [P086_639D_bear_and_contribution](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P086_639D_bear_and_contribution.c) | 614 | 547 | 265 | 完成 |
| shard09 | [P090_1027G_x_mouse_in_the_campus](../../QCP_examples/LLM_bench/Codeforces/examples_shard09/P090_1027G_x_mouse_in_the_campus.c) | 305 | 678 | 103 | 完成 |
| Algorithms | [coin_change](../../QCP_examples/LLM_bench/Algorithms/coin_change/coin_change.c) | 61 | 29 | 22 | 完成 |
| Algorithms | [container_with_most_water_nlogn](../../QCP_examples/LLM_bench/Algorithms/container_with_most_water_nlogn/container_with_most_water_nlogn.c) | 325 | 231 | 130 | 完成 |
| Algorithms | [energy_necklace](../../QCP_examples/LLM_bench/Algorithms/energy_necklace/energy_necklace.c) | 131 | 56 | 59 | 完成 |
| Algorithms | [house_robber](../../QCP_examples/LLM_bench/Algorithms/house_robber/house_robber.c) | 20 | 33 | 6 | 完成 |
| Algorithms | [huffman_encoding](../../QCP_examples/LLM_bench/Algorithms/huffman_encoding/huffman_encoding.c) | 72 | 98 | 34 | 完成 |
| Algorithms | [kings_game](../../QCP_examples/LLM_bench/Algorithms/kings_game/kings_game.c) | 96 | 61 | 72 | 完成 |
| Algorithms | [matrix_chain_multiplication](../../QCP_examples/LLM_bench/Algorithms/matrix_chain_multiplication/matrix_chain_multiplication.c) | 122 | 66 | 63 | 完成 |
| Algorithms | [maximum_subarray](../../QCP_examples/LLM_bench/Algorithms/maximum_subarray/maximum_subarray.c) | 41 | 20 | 14 | 完成 |
| Algorithms | [merging_stones](../../QCP_examples/LLM_bench/Algorithms/merging_stones/merging_stones.c) | 122 | 102 | 49 | 完成 |
| Algorithms | [multiple_knapsack](../../QCP_examples/LLM_bench/Algorithms/multiple_knapsack/multiple_knapsack.c) | 153 | 163 | 42 | 完成 |
| Algorithms | [non_overlapping_intervals](../../QCP_examples/LLM_bench/Algorithms/non_overlapping_intervals/non_overlapping_intervals.c) | 76 | 83 | 52 | 完成 |
| Algorithms | [rmq](../../QCP_examples/LLM_bench/Algorithms/rmq/rmq.c) | 206 | 207 | 33 | 完成 |
| Algorithms | [rod_cutting](../../QCP_examples/LLM_bench/Algorithms/rod_cutting/rod_cutting.c) | 31 | 22 | 16 | 完成 |
| Algorithms | [split_array_largest_sum](../../QCP_examples/LLM_bench/Algorithms/split_array_largest_sum/split_array_largest_sum.c) | 49 | 48 | 20 | 完成 |
| Algorithms | [super_piano](../../QCP_examples/LLM_bench/Algorithms/super_piano/super_piano.c) | 177 | 74 | 120 | 完成 |
| Algorithms | [zero_one_knapsack](../../QCP_examples/LLM_bench/Algorithms/zero_one_knapsack/zero_one_knapsack.c) | 66 | 61 | 39 | 完成 |
