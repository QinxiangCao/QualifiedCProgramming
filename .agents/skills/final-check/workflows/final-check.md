# 最终发布与检查

只由 main 执行当前 controller action，不创建 subagent。保留 action 的解释器、完整 argv 与 cwd；工具只接受 shell 文本时按实际 shell 引用参数。

## 发布当前 candidate

`vc-proving-verify` 读取当前 group 文件与 accepted plan，机械合并并执行完整 parent 检查。`final-apply` 从该 proving task 的 `proving_merged` 目录读取当前 manual/lib，再次通过 overlay 编译，并检查 statement、prelude、proof mode、安全约束和新增 helper suffix；发布本次 staging 中实际通过检查的规范化源码。不存在需要 owner 维护的 base/worker manifest 或 merge-result 文件。

只发布 exact manual 与 active case lib，合法数量为 0、1 或 2 个文件。Absent role 不创建 placeholder，也不授权删除其他文件。C、goal、auto、goal-check 仍由 annotation generation 更新。

Case lib 经相同导入规范化后必须以完整 annotation seed 的 tokens 开头，已有声明不得改写；seed 后新增的 helper 仍可在当前 candidate 中修正。

发布备份位于 `reports/<run>/final-check/backup`。替换失败或中断时，controller 根据本次 original/candidate 内容安全恢复。遇到第三方修改、危险路径或缺失备份时，保留当前文件和备份并报告 publication conflict；main 不强制覆盖。

## 检查当前义务与证明

`final-check` 对当前 C 独立运行一次 symexec，输出到 `reports/<run>/final-check/symexec-refresh`，不覆盖 proved manual。Controller 检查：

- fresh goal、auto、goal-check 与当前 generated files 一致；
- fresh/proved manual 的 prelude、scope、declaration 顺序、VC 名称、statement 与 split mapping 一致；导入路径按 Coq staging 的同一规则规范化；
- 每个 top-level VC 按当前 plan 的 proof mode 完成；aggressive split 全部完成并以 `LLM_pre_process` 开始，LLM route 未采用的 split 保留生成的 `Abort`；
- 当前源码完整通过 Rocq，case lib 即使未被 goal-check 引用也会编译，其 import closure 不得触达当前 generated artifacts；
- 不含 Admitted、额外 Axiom、unsafe typing、rollback 控制或禁用 lemma；危险命令放在 Proof 内也会检查；新增/复用 helper 使用当前 group suffix；
- 用户指定 spec 保持文本级 freeze 约束。

依赖使用同一 plan 格式与当前 native backend。历史文件只作参考，旧检查结果不能代替当前检查。Raw manual 不存在时，proved manual 也必须不存在；零 VC 不跳过完整 parent/final 检查。Helper 新增范围以本次发布的 original backup 为准。

## 清理、恢复与结果

Controller 只清理 exact current module 的副产物文件及本 run 非 `_coq_builds` 区域的副产物。保留 source、基础库 artifacts、history、report、candidate、backup，以及名字看似副产物的目录。扫描失败或 junction/reparse 重定向必须报告。

证明、结构或 freshness 检查失败时，controller 尝试安全回滚本次发布；成功后当前 action 回到 `final-apply`。有冲突时停止自动覆盖。暂停或其他任务状态变化后，重新读取当前 action，不沿用旧的检查结果继续发布。全部通过后才返回 `done`。
