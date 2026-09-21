# Group Worker 证明流程

## 领取与当前输入

只使用当前 claim/handoff、本 skill 和其中指定的资料。读完整 `group_worker_input.md` 与相关证明知识文档；不要读取 controller state、调度 sibling 或推进 parent 阶段。偶然多读文件本身不是 blocker，越界写入和依赖当前 sibling 输出仍然禁止。

Handoff 给出 group、固定 copied manual、可选 group_worker_lib、当前 proof mode、assigned witnesses、helper suffix、报告和命令。这些内容直接从当前 canonical 文件和 accepted plan 派生。每次命令重新读取当前输入，owner 不创建或维护额外 assignment 文件。

## 按需复用历史证明

Handoff 给出本 run 的历史只读路径；脚本只复制当前 canonical manual/lib，不预填历史 proof：

1. 按当前 witness、命题与 proof mode 搜索先前 proving round；已有证明也可在 annotation history 的各 attempt `before` 目录中查找。不要扫描其他 run 或读取当前 sibling。
2. 自行判断是否复制、改写或重做。只修改本组允许的 proof spans；需要的 helper 在本组 lib 中使用当前 suffix，并自行同步引用。
3. 使用 handoff 的 development/check 验证当前定义、导入、premise 与 split route。历史中的 `Qed` 不能代替当前检查。
4. 可在 `proof_reuse.md` 简短记录来源和决定；它没有固定格式，缺失或为空不阻断交付。

同名但命题变化、proof mode 变化、未完成 helper、危险假设或禁用 tactic 都不能当作现成证明。普通 tactic 失败先在当前组修正；只有实际 premise/resource 缺口才交 annotation blocker。

## 写入边界与 proof mode

只写本组 assigned top-level proof spans、aggressive route 的 assigned split spans、交接提供的 group_worker_lib、debug script 和报告。Statement、declaration 顺序、prelude、unassigned proof、main root、history、plan、state 和 sibling 文件只读。当前 lib 的 seed declaration 也不可修改。

- `aggressive_pre_process`：先证明全部 split goals，各自以 `LLM_pre_process ltac:(...)` 开始；top-level 使用 aggressive_pre_process，按当前规则仅用 `Goal_apply` 对应 split lemma 完成各分支。Controller 检查 mode、完整性和 Rocq，不做 Goal_apply 的逐字文本门禁。
- `LLM_pre_process`：只证明 top-level，使用 `LLM_pre_process ltac:(...)`；其 split blocks 保留 generated `Proof. Abort.` token。
- 禁止 `entailer!`、别名 `pre_process`、Admitted、额外 Axiom、unsafe typing、rollback 控制和禁用 lemma。

格式、注释、CRLF/LF 与 EOF 换行不是 proof token 修改。group directory 最终只有 copied manual 和交接提供的可选 lib；debug/build/report 各在给定位置。

## Helpers 与依赖

只有交接提供 group_worker_lib 时才能追加完整证明的 Lemma/Theorem/Fact/Remark 和所需官方 Rocq import。全部新增、复制、改写 helper 均使用当前 suffix；`visibility` 只是复用意图，不触发 promotion。合并只拼接已验证的 proof/helper，命名冲突由 owner 修改；脚本不自动改名或改写引用。

项目依赖来自当前 canonical inputs 和 controller 准备的闭包。需要新的项目依赖或更改 seed/spec 时，精确报告依赖或 annotation 边界；不要自己运行 raw Dune/Make/coqdep、改 load path、导入 generated/current/sibling 模块或修改 main library。lib 缺失时不创建 placeholder，不新增 helper/import。

## 检查与交付

按照 handoff 使用 coq-debug、group-development 和 group-check。Controller 使用统一依赖 plan 刷新所需 native dependencies，实际编译当前 source。Group check 只检查本组 wrapper 及其依赖，不要求其他 groups 的 proof 完成；parent/final 负责全量组合。

修复完成后先写说明，再写 terminal report，停止全部写入，由 main 执行 finalize-delivery。`finalize-delivery` 一次完成当前报告和本组文件的验收：completed 必须通过结构与本组 Rocq；annotation-gap 检查准确 VC/位置与安全写入边界，不要求不可证目标完成。Report-only repair 只修改说明/报告；formal repair 在同一 owner 和目录中继续。每次新交付均重新检查当前 proof。重复工具错误没有自动次数门禁或换轮；根据诊断原地修复或报告明确 infrastructure blocker。

成功报告严格为 `{"status":"completed"}`。Blocked 报告严格增加一个 blocker，其字段为 `failure_class`、`kind`、`vcs`、`message`、`repair_boundary`。VC 条目严格包含 `name`、`parent`、`annotation_location`。

具体 annotation gap 必须使用 `failure_class: annotation-gap`，在非空 `group_worker_output.md` 说明已有 premise、不可推出的结论、已尝试路径和必须修改的 annotation/spec 位置；`vcs` 指向当前 manual 的实际 assigned VC。该缺口是本组终态，停止越界修正，不判断或控制 sibling。工具/报告问题不得伪装为 annotation gap。普通 proof 搜索失败不作为终态 blocker。
