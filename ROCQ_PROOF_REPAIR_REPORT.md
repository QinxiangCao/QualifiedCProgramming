# Rocq 证明修复汇报

仅记录本轮 `Rocq/examples/Applications_human/{CDCL,minisat}` 修复；除特别说明外，证明均经 Rocq MCP 确认完成。

## minisat

### 公共库、策略与目标接口

- `binary_scratch_open_for_write`、`learnt_sort_rep_focus_one__clause_cmp`：旧空间消去未闭合；按实际列表形状转换数组段并补全 `cancel`。
- `solver_qcp_strategy{72,73,76}_correctness`：地址算术未归约 `sizeof(INT)` 或使用了过期蕴含结构；先求值类型大小，再用 `lia`、`cancel` 和 `entailer!` 收尾。
- `msat_binary_conflict_exit_package`：`nia` 无法消去抽象指针宽度；改用指针宽度为正和乘法单调性完成索引边界。
- `msat_reducedb_remove_current` 等指针大小调用：固定 4 字节旧引理已删除；统一改用当前架构的 `eval_ptr_size`。
- `msat_addclause_dedup_keep`：tactic 只识别旧数组替换式；兼容当前上下文中的直接读取事实。
- state-search incremental specs：公式变量遮蔽函数语义参数；重命名绑定以恢复 `HoareFun` 类型。
- `lit_neg_*`、`lit_var_*` 与 propagate 聚合接口：生成 VC 已重编号；同步当前目标名并删除失效声明。
- manual 分片：propagate、state-search、support 分别拆为 6、8、4 个 part，并由原入口统一导入。

### support manual

- `order_update_entail_wit_{1,4}`：显式 split 实参顺序过期；改为整体证明并停用旧 helper。
- `lit_neg_return_wit_{1_bounded,3_sentinel}`、`lit_var_return_wit_{3_original,1_bounded_index}`：VC 分支重编号；迁移证明并同步聚合别名。
- `selectionsort_*`、`clause_new_entail_wit_1`、`order_select_entail_wit_12_{1,2,4}`：split 实参或局部 tactic 过期；改用无参 `Goal_apply`、整体证明或内联展开。

### analysis manual

- `solver_lit_removable_entail_wit_9`、`solver_lit_removable_which_implies_wit_{4,8,12}`：split 参数顺序及旧 helper 目标失配；改为基于当前栈、数组段和整数范围的整体证明。
- `solver_analyze_which_implies_wit_{20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35}`：正文与当前 VC 编号或上下文错位；按现行表示、数组焦点和不变量迁移或重写证明并移除过期编号。
- `solver_lit_removable_entail_wit_13_1`：预处理后旧 `replace_Znth` 形状已消失；删除冗余 rewrite 和 `nia`。
- `solver_analyze_which_implies_wit_{6,26,29,34}`：目标已由 `proof_auto.v` 提供；删除 manual 重复定义并保留 auto 实现。

### propagate manual

- `solver_propagate_which_implies_wit_{16,46,47,48,49,50,51,52,53,54,55,56,57,58}`：旧正文对应早期 VC 上下文或错误编号；按当前扫描、enqueue、watch-list 和数组分段语义重建证明。
- `solver_propagate_entail_wit_{5_1_scan_move,6_1_scan_same,7_scan_move,8_scan_same,14_scan_same,15_{1,2}_unit_conflict_copy,16_2_unit_conflict_copy,17_unit_conflict,18_{1,2}_unit_*}`：旧数组形状、指针大小或分支编号失配；使用现行读取事实、正确分支和空间 frame 收尾。
- `solver_propagate_partial_solve_wit_{34,35,38,41,44,47,50,51,53,54,55,56,76,78,84,85,86,87,88,91}_*`：预处理已化简或关闭目标，遗留 rewrite、bullet 和 tactic 因而失败；删除死步骤或改用可选 rewrite。
- `solver_propagate_partial_solve_wit_{433,434,437,443,446}_*`：旧编号 441、446、447、450、451 已迁移；同步现行名称并复用适配后的证明。
- `solver_propagate_partial_solve_wit_438_unit_same_pure`：缺少 enqueue 前提；由扫描语义和 solver shape 补齐。
- `solver_propagate_partial_solve_wit_442_unit_move_pure`：规范化子句长度未折回；重写长度后复用现有扫描不变式。
- `solver_propagate_entail_wit_{17_1,17_2}_unit_conflict_copy`：旧目标已由当前 `wit_15_{1,2}` 覆盖；删除过期重复证明。
- `solver_propagate_entail_wit_18_{1,2}_unit_*`、`solver_propagate_partial_solve_wit_{53,54,55,56,84,85,86,87,444,445}_*`：对应目标已有 auto 证明；manual 改为停用或删除重复项。

### state-search manual

- `assume_entail_wit_2`、`solver_addclause_return_wit_7`、`solver_simplify_{return_wit_{1,2,3},entail_wit_{2_1,2_2}}`、`solver_solve_entail_wit_5_4`、`solver_search_entail_wit_8`：显式 split 参数顺序过期；改为整体证明、无参 `Goal_apply` 或停用旧 helper。
- `solver_solve_entail_wit_{5_1,5_2,5_3,8_1,8_2}`、`act_var_bump_entail_wit_1*`、`clause_simplify_*`：split 参数落后于当前上下文；改为整体证明或无参 `Goal_apply`。
- `enqueue_partial_solve_wit_{2,5,6,7}_pure`、`enqueue_return_wit_{2,5}`：旧脚本处理已消失的数组更新式或误判纯合取层级；按当前假设拆分、删除死步骤并将共享 rewrite 改为可选。
- `enqueue_partial_solve_wit_{8,9}_pure`：目标已有 auto 证明；删除 manual 重复定义及聚合别名。
- `solver_addclause_entail_wit_7_2`、`solver_addclause_return_wit_{3,4,5,8}`、`solver_setnvars_entail_wit_3_2`：旧 dedup/split 调用与当前目标失配；改用现行读取事实、无参 `Goal_apply` 或直接构造状态。
- `solver_{nclauses,nconflicts,nvars,solve}_*_spec_entail_*_incremental_spec`：目标改名且返回量词/wand 形状变化；按当前 frame 和分支恢复 ownership。
- `solver_addclause_addclause_spec_entail_solver_addclause_incremental_spec`：旧名称、wand 展开和结果 existential 过期；按当前接口重建桥接证明。
- `solver_qcp_{goal,goal_check,proof_auto,proof_manual*}.v`：总入口已被四组拆分文件取代且无外部引用；删除冗余聚合链。

## CDCL

- `CDCL_qcp_goal.v`、`CDCL_qcp_goal_check.v`：内置数组策略已迁移命名空间且实现未 Include；改用 `SimpleC.Verification.BuiltIn` 并补入策略证明。
- `bcp_entail_wit_10_{1,2,3,5}`：旧 `poly_store_unfold` tactic 已不存在；定义等价的当前展开并复用到同类证明。
- `cdcl_solver_entail_wit_6_2`：误用 `derivable1s_truep_intros` 处理空间合取；改为 `derivable1s_andp_intros`。
