# LLM_bench 第二批与其余基础层案例迁移

> 2026-10-13 目录整理：本文中的审计及历史兼容记录描述当时的验证结果。独立的 `*_proof_audit.lean`、`*_proof_historical.lean`、`*_historical_goals.lean` 和 `*_vc_compat.lean` 已移除；当前证明需要的辅助引理归入对应 lib 或 manual/partN，未使用的旧证明已删除。`proof_helpers`、`length_proofs`、`array_views` 的内容已合入对应 lib。

按后续要求，已删除 `DependencyChecks.lean`、`SecondBatchChecks.lean`、`SecondBatchSemantics.lean`、`SecondBatchBehaviorChecks.lean`、`ThirdBatchChecks.lean` 五个聚合或回归测试文件。LLM_bench 总入口直接导入 107 个案例的 goal_check。下文相关 API、公理及行为检查数字保留为历史验收记录；当前 Python 检查脚本检查源码哈希、清单状态与显式证明空缺集合，不再运行已删除的聚合检查。

截至 2026-09-06，本批 34 个案例全部完成案例库、生成 VC、manual、公开接口和证明依赖审计：2,958 条源 `Qed` 均有完整 Lean 证明，1,952 条源 auto `Admitted` 仍明确保留。连同首批八例，全 42 例的生成一致性、严格源清单检查及 `lake build LLMBench` 聚合构建均已通过。迁移完成不表示原有自动证明空缺已经补证。

后续接口整理：升级新版库后，Arch32 改为直接导入 `SimpleC.SL.CArch`，数组未初始化谓词直接使用 `naive_C_Rules.IntArray2.undef_full`；旧 `Architecture32.lean`、`ArrayCompatibility.lean` 已删除。下文保留第二批当时的导出兼容检查记录，当前[依赖清单](llm_bench_second_batch_dependencies.json)记录 34 个源 API、12 条源 Qed、13 条已证辅助引理，额外旧接口导出为 0。数学模块已上移至 AUXLib；案例与检查直接使用 prime_alt，原 prime_iff_legacy 辅助桥接已移除。

## 来源、范围和计数

- 仓库基线：`qcp-binary-democases` 提交 `e95ad5cea97c21f90e12a7434ccb65a06e53254c`；不改变既有基础库迁移的 `annotated_simplec` 基线。
- 子模块：`mcp/rocq-mcp` 固定于 `674f21a5aed9604359741c4d51dd5096f4cc8cec`，迁移时未初始化；案例源文件读取仓库内 `Rocq/`。
- 工具链：Lean `leanprover/lean4:v4.25.2`；新增标准库依赖片段依据 Coq 8.20.1（OCaml 5.2.1），具体源文件 SHA-256 另有记录。
- [范围表](llm_bench_second_batch_scope.json)的 B1 是 `stack`、`majority_element`、`container_with_most_water_linear`、`sliding_window_maximum`，其余 30 个属于 B2 基础层。本批按所需依赖片段扩展，未整体升级 Lean 基础库。
- [逐声明清单](llm_bench_second_batch_inventory.json)覆盖 172 个 Coq 源文件，保存路径、SHA-256、声明种类、Lean 名称和迁移状态；[依赖清单](llm_bench_second_batch_dependencies.json)单独限定跨文件依赖范围。首批八例的记录仍见[原报告](llm_bench_first_eight_migration.md)。

下表统计 Coq **活动声明**，不按 Lean 辅助证明数量计数。34 例源 auto 均没有 `Qed`，共 1,952 条 `Admitted`；源 lib/manual 没有 `Admitted`，也没有 `Defined` 终结的声明。下表 lib/manual 均为已迁移并完成审计的源 `Qed` 数量。

| 案例 | lib Qed | manual Qed | auto Admitted | 审计状态 |
| --- | ---: | ---: | ---: | --- |
| `stack` | 5 | 16 | 14 | 已通过 |
| `majority_element` | 12 | 5 | 17 | 已通过 |
| `container_with_most_water_linear` | 4 | 27 | 20 | 已通过 |
| `sliding_window_maximum` | 10 | 47 | 23 | 已通过 |
| `annoying_math_homework` | 35 | 97 | 117 | 已通过 |
| `bucket_sort` | 62 | 78 | 53 | 已通过 |
| `catalan_numbers` | 20 | 30 | 44 | 已通过 |
| `chinese_remainder_theorem` | 23 | 42 | 19 | 已通过 |
| `choosing_inns` | 39 | 43 | 35 | 已通过 |
| `concatenating_numbers` | 149 | 54 | 98 | 已通过 |
| `concatenating_numbers_dp` | 82 | 92 | 65 | 已通过 |
| `counting_sort` | 49 | 44 | 35 | 已通过 |
| `discretize` | 55 | 24 | 72 | 已通过 |
| `edit_strings` | 92 | 155 | 150 | 已通过 |
| `euler_theorem_inverse` | 43 | 56 | 41 | 已通过 |
| `extended_chinese_remainder_theorem` | 18 | 53 | 18 | 已通过 |
| `integer_divide` | 8 | 11 | 18 | 已通过 |
| `lcs_n` | 20 | 21 | 63 | 已通过 |
| `lucas_theorem` | 50 | 66 | 42 | 已通过 |
| `minimal_representation` | 17 | 36 | 41 | 已通过 |
| `quicksort_hoare_fill_index` | 0 | 41 | 41 | 已通过 |
| `quicksort_hoare_fill_index2` | 0 | 41 | 47 | 已通过 |
| `quicksort_hoare_swap_index` | 61 | 37 | 41 | 已通过 |
| `quicksort_hoare_swap_index2` | 0 | 37 | 47 | 已通过 |
| `quicksort_lomuto_index` | 0 | 31 | 41 | 已通过 |
| `sieve_of_eratosthenes` | 13 | 16 | 23 | 已通过 |
| `sieve_of_euler` | 33 | 39 | 28 | 已通过 |
| `sort_point` | 73 | 80 | 213 | 已通过 |
| `stock_trading` | 57 | 176 | 174 | 已通过 |
| `binary_indexed_tree` | 22 | 25 | 12 | 已通过 |
| `priority_queue` | 73 | 45 | 69 | 已通过 |
| `priority_queue_decrease_key` | 50 | 37 | 99 | 已通过 |
| `priority_queue_index` | 62 | 43 | 86 | 已通过 |
| `minisat` | 4 | 72 | 46 | 已通过 |

34 例合计 1,241 条库 `Qed` 加 1,717 条 manual `Qed`，共 2,958 条已完成证明，另保留 1,952 条 auto `Admitted`。这些数值已独立从去除嵌套注释后的 Coq 文件终结符复核，与逐声明清单逐文件一致。

DP 已完成 104 个库 API、92 个 manual API 的精确检查，以及 82 条库 `Qed` 加 92 条 manual `Qed` 的全部递归证明闭包审计；65 条 auto 空缺保留。其 26 个组合证明中 60 次实际 `Goal_apply` 调用通过，没有 `exact` 兜底，最终 `goal_check` 构建为 137 jobs。

`priority_queue` 的 73 条库证明包括 72 条 `Lemma` 和一条 `#[export] Instance multiset_equiv_Equivalence`，不能漏算实例。四个 quicksort 行的库计数为 0，表示本例源文件没有活动库 `Qed`；案例的同级 Lean 库仍承接源导入关系。`edit_strings` 的 155 条 manual 包括 153 条 VC 证明及源 manual 中两条公开 scratch-count 辅助引理，不能只按 `proof_of_` 名称统计。

`stock_trading` 保持原有五个 manual 子模块，由同级 `stock_trading_proof_manual.lean` 导入并导出。五份源文件的 `Qed` 数分别为：

| 源 manual 文件 | Qed |
| --- | ---: |
| `stock_trading_proof_manual_part1.v` | 64 |
| `stock_trading_proof_manual_part2.v` | 37 |
| `stock_trading_proof_manual_part3.v` | 11 |
| `stock_trading_proof_manual_part4.v` | 25 |
| `stock_trading_proof_manual_part5.v` | 39 |
| 合计 | 176 |

主 manual 文件本身没有新增源 `Qed`。另有 `stock_trading_proof_helpers.lean` 提供五条已证明的分离逻辑及语义组合辅助引理；它们不充作源声明数量。该例 57 条库证明与 176 条 manual 共 233 条源 `Qed` 的递归依赖审计通过，174 条 auto 空缺保留。`edit_strings` 同样完成 92 加 155 共 247 条源 `Qed` 的审计，150 条 auto 空缺保留。

## 目录、定义和公开接口

案例位于 `Lean/examples/SimpleC/EE/LLM_bench/{Algorithms,Data_structures,Engineering}/<case>/`。`lib`、`goal`、`proof_auto`、`proof_manual`、`goal_check` 保持同级；quicksort 案例沿用源文件的 `quicksort_*.lean` 文件名，`Engineering/minisat` 沿用 `vec_*.lean`。stock 的五个 manual 子模块和辅助模块是同一目录内的扩展，没有取代主 manual 入口。

C 文件仅补充案例库的 `Import Lean` 注解及空行；全 42 例已核对算法和原契约保持不变，`Rocq/` 的 Git 差异为空。生成的 `VC_Correct` 是带全部所需证明字段的 Lean 结构体，`VC_Correctness` 逐字段组装证明。Coq `Module Type` 中的 `Axiom` 是接口要求，在这里没有变成额外的全局公理。

扩展遵循源定义的递归体、参数顺序、量词、构造器和类型实例。典型接口如下：

- `priority_queue` 与 `priority_queue_index` 各自保留独立的 `multiset` record，字段承载任意 `List A`，`multiset_equiv` 仍为列表 `Permutation`，没有替换成商类型。公开 `Build_multiset (A : Type) (mlist : List A)` 保持显式的类型参数，投影 `mlist {A}` 保持隐式类型参数。透明 `@[match_pattern]` 构造器包装支持源名称下的构造和模式匹配。普通 priority queue 的 `multiset_equiv_Equivalence` 是实际的 `AUXLib.Equivalence` 实例，`#synth AUXLib.Equivalence (@multiset_equiv Int)` 已通过；index 源没有该实例，未额外添加。
- stock 的三个 `StockTradingHistory_*` 和 edit 的五个 `EditGreedyConsumedPrefix_*` 均包装真实 inductive 构造器，保留源显式参数，并通过构造与模式匹配探针。包装声明属于 `abbrev`，底层构造器位于 Lean inductive 命名空间；这是公开表示适配，不是定理或新公理。
- `lcs_n`、`counting_sort` 的 `Some {A : Type u} (x : A)`、`None {A : Type u}` 是案例局部透明别名，仍表示标准 `Option`。`stock_trading` 与 decrease-key 的 `_List_Z := List Int`，以及 counting-sort 的 `_App_option_Z := Option Int`，只承接生成器给嵌套类型取的名字。生成 VC 中任意 `default` 的全称量词全部保留，未把它们固定为空列表或 `none`。
- `integer_divide` 现在使用 [Prime.lean](../auxlibs/AUXLib/Prime.lean) 中忠实的 Coq `prime` inductive：构造器保留 `1 < p` 和区间内相对互素两个条件。`prime_alt` 保持源 `prime' p ↔ prime p` 方向。到既有 QCP demo 素数谓词的关系在案例和检查中直接使用 `prime_alt` 建立，基础库不再依赖 demo；案例的公开 `prime` 不再直接指向 demo 的另一种定义。`HdRel`、`Sorted` 仍保持源构造器结构。

[依赖清单](llm_bench_second_batch_dependencies.json)列出 29 个所达源 API，其中 10 条源 `Qed`；另外登记 14 条已证明的兼容引理及一个透明公开导出。依赖包含 `Z.lcm`、`Z.Bezout`、32 位 C 架构常量、`Zis_gcd`/`rel_prime`、`prime`、`StronglySorted`、`upperbound`、`fact` 和下述 DP 定义的有限片段。`Z.lcm` 保留源表达式 `abs (a * (b / gcd a b))`；对现有整数 LCM 的关系在证明中处理。`Z.div`/`Z.modulo` 与 `Z.quot`/`Z.rem` 的两套除余语义仍严格区分，负数边界有行为探针。

DP 引入的三个所达定义是 Coq `ZArith/BinIntDef.v` 的 `Z.log2`、`Z.eqb`，以及 `Lists/List.v` 的 `list_power`。`Z.log2` 保留非正输入返回 0 的行为，`Z.eqb` 保留布尔相等接口，`list_power` 保留源递归枚举。这三项已纳入上述 29 个源 API；源文件哈希和依赖聚合检查均已通过。

stock 用到的 `IntArray2.undef_full` 原来只缺公开导出别名：Coq 路径是 `Array2Lib.v` 的 `IntArray2` 模块导出及 `Array2LibCore.v` 的定义，Lean 的 `naive_C_Rules.IntArray2.undef_full` 和 `full_to_undef_full` 定理已经存在。本批只在公开 `IntArray2` 命名空间补透明 `abbrev`。三参数类型检查、与原核心定义的 `rfl`、以及实际 `sep_apply ...full_to_undef_full; cancel` 调用都通过；没有新建或弱化数组谓词。

## 生成差异和原契约的边界

生成脚本的确定性后处理包含 Lean 关键字 `prefix` 的引号化，以及 `intArray` 断言中 `replace_Znth` 替换值的 `Int` 字面量注解。后者覆盖单/双括号正负整数，如 `(0)`、`(-1)`、`((-1))`，并支持当前案例中带括号的复合索引。该规则限于以 `intArray.` 断言开头的行，不改 `PtrArray` 或任意纯逻辑项；幂等性和非目标行保留均已检查。这些处理补足语法和类型信息，不改变源 VC 的逻辑。

DP 的移位安全 VC 还将生成的 `Int` 绑定变量用作 `^` 的指数。只有检测到这种情况时，后处理才在现有 `open scoped SimpleC.SL.SAC` 行加入 `CoqZ`，启用已存在的 Coq `Z.pow` 实例，保留整数指数的含义。该规则已用于实际 DP goal 并通过构建，其他 41 个已登记案例的生成结果未受影响；没有全局替换自然数指数的幂或新增幂实例。

decrease-key 的存档 Coq VC 与当前生成结果另有 **12 处语义表达差异**，不能归类为字面量格式差异。使用同一个 C 文件分别重新生成 Coq 和 Lean，200 个当前 VC 经语法归一后逐项一致；旧 Coq 存档与新 Coq 之间正好有这 12 处。存档没有被覆盖。

原 `priority_queue_decrease_key_vc_compat.lean`（已移除）独立逐字对应翻译旧 Coq 的 12 个命题到 `SourceVC`，保留源位置与哈希，并证明每个旧命题与当前命题双向等价。每行涵盖完整 VC 及对应 split VC，因此下表六组共 12 条 `↔`：

| 完整 VC（共同前缀 `pqdk_`） | 对应 split | 原前提提供的等式 |
| --- | --- | --- |
| `sift_up_entail_wit_4` | `split_goal_1` | `PreH11 : tmp_data = Znth parent data_values_2 0` |
| `sift_down_entail_wit_3_1` | `split_goal_1` | `PreH8 : right = left + 1` |
| `sift_down_entail_wit_3_2` | `split_goal_1` | `PreH8 : smallest = left` |
| `sift_down_entail_wit_3_3` | `split_goal_1` | `PreH9 : smallest = left` |
| `sift_down_entail_wit_4` | `split_goal_6` | `PreH6 : left = current * 2 + 1` |
| `sift_down_entail_wit_5` | `split_goal_1` | `PreH15 : tmp_data = Znth current data_values_2 0` |

等价证明分别展开原命题、保留原析取分支及全部量词，在两个方向使用上述原有等式；没有向 VC 添加条件，也没有盲目替换变量来跳过对比。全部 12 条等价证明的递归公理审计没有 `sorryAx`。

最终生成声明诊断另覆盖本批 34 例的 4,095 个 VC：名称、顺序和计数全部一致，4,083 个经语法归一后的 token 对照一致，余下 12 个正是上述 decrease-key 等价证明覆盖的差异，没有新增或未解决的差异。`SourceVC` 的 12 个定义也以保留括号的逐 token 翻译对照重新核验，与归档文本及源哈希一致。4,095 项是归一化生成对照诊断，不是 4,095 条形式等价证明；上述 12 条 `↔` 才是额外由 Lean 内核检查的双向等价证明。

`edit_strings` 的源 C 契约已经要求 `EditGreedyCompletedMaximumFacts`：任意满足完成前缀状态的结果都满足可行性与最优性。Lean 保留这一假设及 `EditGreedyCompletedStateFacts`，最终 manual 使用相应已证明的转换定理。因此这里完成的是原条件契约的迁移，不能将其解释为额外证明了无该假设的全局贪心最优性。stock 的 `StockPortfolioValue`、`StockDaysDone` 和最终最大收益结论也保持源可行性与上界含义，未降成单纯数组形状或局部数值界。

## 实际策略兼容性

手工证明实际执行现有 Lean 分离逻辑策略，包括 `pre_process`、`aggressive_pre_process`、`Exists`、`sep_apply`、`split_pure_spatial`、`dump_pre_spatial`、`cancel` 和 `Goal_apply`；普通库定理允许使用 Lean 的归纳、重写与算术证明。没有把手工验证文件中的策略换成只为单例同名的占位实现。

Coq Ltac 的参数搜索、分支顺序和 Lean matcher 并非完全一致。复合 VC 可以选择生成命题已有的分支，再显式提供 split 定理的参数。若 split 的结论本身带 `∀`，需要先引入结果变量及其范围前提，再调用完整实例化的 `Goal_apply`。stock、edit 和两种 concatenating-numbers 的相关生产证明已经通过实际调用验证：普通版本有 14 处实际 `Goal_apply`，DP 有 60 处，两者均无 `exact` 兜底。另一个只给裸全称定理的 concatenating-numbers 探针在 4,000,000 heartbeat 限制下于 `whnf` 超时，因此仍不声称完整 Ltac 调用兼容。

源手工文件的局部策略也被记录：majority 的 `grab`、choosing_inns 的 `choosing_input_safe_lia` 和三个 priority-queue 案例的 `finish_entail`。其中 `grab H pat` 的 Lean 参数是类型项，不支持任意 Coq Ltac 模式语法。公开差异和调用限制见[差异记录](migration_inconsistencies.md#llm_bench-second-batch-and-remaining-foundation-cases)。

## 检查入口与当前结果

在仓库根目录执行以下命令，检查全部 42 个已登记案例：

```sh
python3 scripts/generate-llm-bench-lean.py --check
python3 scripts/check-llm-bench-lean.py --coq-lib /path/to/Coq-8.20.1/theories
lake build LLMBench
```

`--coq-lib` 应指向 Coq 8.20.1 的 `theories` 目录，以复核所达外部标准库源文件哈希。省略它时仅跳过这些外部标准库源哈希；仓库内源哈希、声明和空缺集合仍检查，Lean 依赖证明闭包仍由构建编译检查。生成一致性也可按案例只读复核，例如：

```sh
python3 scripts/generate-llm-bench-lean.py --check stock_trading edit_strings priority_queue_decrease_key
```

`goal`、`goal_check` 由生成器更新，已有 lib、auto、manual 保留。`--check` 不写文件；`--initialize-proofs` 只在缺少证明文件时建立模板，不覆盖现有证明。全量验收使用严格检查模式，没有以 `--completed-only` 排除案例。

全部 34 例已逐案通过相应构建和源 `Qed` 的递归依赖审计。stock 的最终 `goal_check` 构建为 138 jobs，edit 为 136 jobs，concatenating-numbers 为 132 jobs，DP 为 137 jobs；stock 的 444 个源 API、edit 的 432 个源 API 均有实际类型检查。`SecondBatchChecks.lean`（已删除）统一检查本批 12,346 个源 API 与 2,958 条源 `Qed` 的递归闭包。源 Qed 的证明闭包没有 `sorryAx`，未引入源外 `axiom`、`admit` 或 `unsafe`。自动文件的原有空缺有明确 Coq 来源；包含它们的整体正确性结构不代表无条件完成全部 VC。

`SecondBatchBehaviorChecks.lean`（已删除）已汇集 34 个案例命名空间中的 366 项行为探针，175 jobs 构建通过。探针覆盖已选定的边界求值、定义展开、构造及模式匹配、类型实例和实际分离逻辑调用；DP 的行为探针覆盖位扫描及输出位操作片段。行为回归与完整 API、证明闭包检查共同纳入聚合构建。

`DependencyChecks.lean`（已删除）已检查上述 29 个源 API、一个公开导出、10 条源 `Qed` 和 14 条额外已证明兼容引理；14 条是原两条兼容引理加 decrease-key 的 12 条旧/新 VC 等价证明。等价证明使用 `collectAxioms` 强制检查递归依赖，`IntArray2.undef_full` 检查透明导出。源哈希核验及该模块的 146 jobs 构建均通过。

最终全 42 例验收通过：重新生成 `--check` 无漂移；严格 Python 检查确认源哈希一致，13,167 个 API 与检查模块清单一致，3,132 条源 `Qed`/`Defined` 加首批 5 条已补证的源 `Admitted` 纳入已证明声明审计，继承空缺精确为 2,092 条。其中 3,132 为首批 174 加本批 2,958，2,092 为首批 140 加本批 1,952。`lake build LLMBench` 的 361 jobs 聚合构建通过，当时包含首批聚合检查（现已删除）、本批全部 `SecondBatchChecks`、`DependencyChecks` 和 366 项行为探针。
