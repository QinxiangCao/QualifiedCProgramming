# Hashtable 按函数验证与合并计划

## 1. 目标

本计划最初将创建/插入/查询与引用查询/删除/释放两个代码分片按函数验证，
随后合并为一个完整实现。两个历史分片现已删除。

最终正式 C 文件放置在：

- `QCP_examples/Applications_human/hashtable/hashtbl.c`

最终 Rocq 文件放置在：

- `Rocq/examples/Applications_human/hashtable/`

当前 specification 作为已认可的验证基线。只有在单函数 manual VC 被确认语义不可证时，才回到 specification 或 annotation 层调整。

所有新写 annotation 必须重新分析，不得使用 `which implies`。

## 2. 基本执行单位

每一个带函数体的函数作为一个独立验证任务。每个任务应包含：

1. 只保留目标函数、必要类型定义和被调用函数合同的单函数 C 文件。
2. 根据函数语义重新填写 annotation，不复制 `which implies`。
3. 运行 canonical symbolic execution，并确认执行到文件尾。
4. 检查所有 generated manual VC 的语义可证性。
5. 完成该函数全部 manual witness 的 Rocq 证明。
6. 通过该任务对应的 fixed `coqc_check`。
7. 确认 manual proof 中没有 `Admitted.`、额外 `Axiom` 或 helper declaration。
8. 将必要 helper 放入该任务的 `case_lib`，并避免与其他函数任务重名。
9. 保存可供最终合并追踪的 annotation、generated files、proof 和检查证据。

各函数任务可以使用独立 controller run；单函数验证通过不等于整体文件已经通过，最终仍需执行一次完整的集成验证。

## 3. 公共定义和外部函数合同

拆分任务前先整理一份公共基础层，供所有单函数文件使用：

- `struct blist`
- `struct hashtbl`
- bucket 数量 `211`
- 公共 separation-logic predicates
- 公共 map/spec declarations

以下函数只有外部合同，不在本计划中证明函数体：

- `malloc_blist_array`
- `malloc_hashtbl`
- `malloc_blist`
- `hash_string`
- `string_equal`
- `free_string`
- `free_blist_array`
- `free_blist`
- `free_hashtbl_struct`

`hash_string` 和 `string_equal` 在两个现有源文件中重复声明且合同不完全一致。开始单函数任务前，应统一为一份能够支持全部调用点的公共合同。两个 `hashtbl_def.h` 的声明也应合并为一个正式版本，不能在不同任务中依赖相互矛盾的定义。

## 4. 函数任务清单

### H01：`create_bucks`

- 来源：原创建/插入/查询分片
- 直接依赖：`malloc_blist_array`
- 验证重点：数组分配、循环初始化范围、最终 211 个 bucket 全部为空。
- 现有 manual VC 参考数：3。

### H02：`init_hashtbl`

- 来源：原创建/插入/查询分片
- 直接依赖：H01 `create_bucks`。
- 验证重点：初始化 `top` 和 `bucks`，建立空表的 `store_hash_skeleton`。
- 现有 manual VC 参考数：1。

### H03：`create_hashtbl`

- 来源：原创建/插入/查询分片
- 直接依赖：`malloc_hashtbl`、H02 `init_hashtbl`。
- 验证重点：结构体分配、初始化调用以及空 value map。
- 现有 manual VC 参考数：1。

### H04：`hashtbl_add`

- 来源：原创建/插入/查询分片
- 直接依赖：`malloc_blist`、`hash_string`。
- 验证重点：新节点字段、bucket 头插、全局双向链表头插，以及 key/value map 同步更新。
- 现有 manual VC 参考数：5，其中 2 个来自旧 `which implies`，重新 annotation 后数量可能变化。

### H05：`hashtbl_find`

- 来源：原创建/插入/查询分片
- 直接依赖：`hash_string`、`string_equal`。
- 验证重点：bucket 遍历、未命中前缀、命中节点 move-to-front 操作、`valid` 和返回值。
- 现有 manual VC 参考数：9，其中 1 个来自旧 `which implies`，重新 annotation 后数量可能变化。

### H06：`hashtbl_findref`

- 来源：原引用查询/删除/释放分片
- 直接依赖：`hash_string`、`string_equal`。
- 验证重点：bucket 遍历、节点地址唯一性、命中时返回 value 字段地址、未命中时返回空指针。
- 现有 accepted annotation 基线已包含 `node_addr_injective`。
- 现有 manual VC 参考数：8。

### H07：`hashtbl_remove`

- 来源：原引用查询/删除/释放分片
- 直接依赖：`hash_string`、`string_equal`。
- 验证重点：bucket 链摘除、双向链表摘除、首节点和中间节点分支、key/value map 删除以及返回资源。
- 现有 accepted annotation 基线已包含 `node_addr_injective`。
- 现有 manual VC 参考数：13。

### H08：`hashtbl_free_blist`

- 来源：原引用查询/删除/释放分片
- 直接依赖：`free_string`、`free_blist`，并递归调用自身。
- 验证重点：递归释放单条 bucket 链、名称和值资源的同步移除、递归终止分支。
- 现有 manual VC 参考数：3。

### H09：`hashtbl_clear`

- 来源：原引用查询/删除/释放分片
- 直接依赖：H08 `hashtbl_free_blist`、`free_blist_array`。
- 验证重点：逐 bucket 释放、循环中的剩余 map、数组 cell 更新、`top`/`bucks` 最终清空。
- 现有 manual VC 参考数：4。

### H10：`free_hashtbl`

- 来源：原引用查询/删除/释放分片
- 直接依赖：H09 `hashtbl_clear`、`free_hashtbl_struct`。
- 验证重点：完整释放组合调用和最终 `emp`。
- 当前没有 manual VC，但仍必须作为独立函数任务通过 symbolic execution 和 fixed `coqc_check`。

## 5. 执行顺序和并行关系

推荐按以下阶段执行：

1. 公共定义与外部合同统一。
2. H01 `create_bucks`。
3. H02 `init_hashtbl`。
4. H03 `create_hashtbl`。
5. H04 `hashtbl_add`、H05 `hashtbl_find`、H06 `hashtbl_findref`、H07 `hashtbl_remove` 可在公共基础稳定后分别执行。
6. H08 `hashtbl_free_blist`。
7. H09 `hashtbl_clear`。
8. H10 `free_hashtbl`。
9. 完整文件合并与集成验证。

有依赖关系的任务必须使用已经验证通过的 callee contract。函数任务之间不直接复制未验收的 manual proof 或临时 helper。

## 6. 最终合并顺序

最终 `hashtbl.c` 按以下顺序拼接：

1. include、公共 Coq imports、Extern 声明和 strategies。
2. 公共类型与常量定义。
3. 去重后的外部函数合同。
4. `create_bucks`。
5. `init_hashtbl`。
6. `create_hashtbl`。
7. `hashtbl_add`。
8. `hashtbl_find`。
9. `hashtbl_findref`。
10. `hashtbl_remove`。
11. `hashtbl_free_blist`。
12. `hashtbl_clear`。
13. `free_hashtbl`。

合并时必须完成以下去重和协调：

- 只保留一个 `hash_string` 合同。
- 只保留一个 `string_equal` 合同。
- 只保留一个 `NBUCK`/bucket-size 定义。
- 合并两个 `hashtbl_def.h` 中确实需要的 Extern 声明。
- 合并各函数任务的 proved helpers，解决名字冲突，并保持 `case_lib` contract。
- 重新生成整体文件的 goal、auto proof 和 manual proof；不得直接把不同单函数 generated 文件机械拼接成最终 generated 文件。

## 7. 集成验证

所有函数任务完成后，针对最终完整 `hashtbl.c` 新建一次集成 run：

1. 对完整文件运行 canonical symbolic execution，确认执行到文件尾。
2. 确认生成文件与最终 C annotation 完全对应。
3. 比对整体 witness 与各单函数已证明 witness；因拼接导致 statement 变化时重新证明对应 witness。
4. 运行完整 fixed `coqc_check`。
5. 检查 `*_proof_manual.v` 只包含当前 case 的 witness proofs。
6. 检查 C 文件中不存在 `which implies`。
7. 检查 manual proof 和 `case_lib` 中不存在 `Admitted.` 或额外 `Axiom`。
8. 检查所有函数合同、公共声明和 helper 均已去重。
9. 执行 final-check freshness、forbidden lemma、case_lib contract 和 cleanup 检查。
10. 只将 controller accepted final candidate 写回正式目录。

## 8. 完成标准

只有同时满足以下条件，整个计划才算完成：

- H01 至 H10 均有独立、可追踪的验证结果。
- 所有带函数体的函数均通过 symbolic execution 和相应 Rocq 检查。
- 最终完整文件通过重新生成后的全部 manual VC。
- 最终 `hashtbl_goal_check.v` 通过 fixed `coqc_check`。
- 正式 C annotation 中没有 `which implies`。
- manual proof 中没有 helper declaration、`Admitted.` 或额外 `Axiom`。
- 最终 `case_lib` 满足 contract，所有 proved helper 来源可追踪。
- 最终交付位于 `Applications_human/hashtable/` 对应的 C 和 Rocq 正式目录。
