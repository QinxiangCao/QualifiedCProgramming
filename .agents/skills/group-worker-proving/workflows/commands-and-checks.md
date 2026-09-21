# Group 命令与检查

只执行 group_worker_input.md 中的 exact argv/cwd：coq-debug、coq-check group-development、coq-check group-check。Main 负责 claim/finalize，worker 不执行 step、retry、merge、parent 或 final。

命令以结构化 JSON 的 `argv` 和 `cwd` 为准，保留解释器、每个参数和参数顺序。优先使用接收参数数组的工具；工具只接收 shell 文本时，按实际 shell 正确引用每个参数：POSIX 使用 shell quoting，PowerShell 使用 `&` 和单引号参数，参数内单引号写成两个单引号。可单独设置 cwd 时使用工具的 cwd 参数。持续等待同一 session 到真实退出；退出码 0 与 JSON status passed 同时成立才是成功。不改 backend/target/flags，也不直接调用 raw Coq/Dune/Make/coqdep。

Controller 派生 copied manual/lib overlay、exact/development build、group wrapper 和唯一 debug script。Current source 在内存中规范化后只写变化内容，每次实际编译。Dune/Make 使用统一依赖 plan 刷新基础依赖；owner 不选择 backend/target/flags。

三类检查共同保护当前 statement、declaration order、unassigned spans、LLM split blocks、seed library、helper suffix/import 和禁止假设。Development 允许 assigned proof 暂时 Abort；exact 要求 assigned witnesses、aggressive splits 和 proof_mode 完整。Group wrapper 不执行全局 goal-check；完整组合由 parent/final 检查。Case lib 即使未被 goal-check 引用也会编译。

历史 proof/helper 和人工复用说明都不作为检查凭据。`finalize-delivery` 对最新文件执行完整验收：completed 必须通过全部结构与本组 Rocq；annotation-gap 必须有准确 blocker/VC/位置、合法写入与安全内容，但不强求不可证目标的完整 Coq 成功。报告或 proof 错误按反馈由同 owner 在当前目录修复。

每个 coq-check/coq-debug 的外部进程共享 900 秒预算；timeout/pause 会终止工具进程并清理子进程；若返回 cleanup 未完成的诊断，保留诊断交回 main。所有路径和文件类型仍由 controller 校验，不用链接、junction 或 reparse point 绕过目录边界。
