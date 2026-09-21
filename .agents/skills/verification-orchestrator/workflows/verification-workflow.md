# 单个 C Case 的流程

## Main 的执行循环

```text
init-run → step → annotation owner → finalize-delivery
→ dune-build → VC-checking owner → finalize-delivery
→ vc-proving-preparing → group owners → finalize-delivery
→ vc-proving-verify → final-apply → final-check → done
```

没有 manual top-level VC 时，依赖准备后直接进入空 group 的 proving 流程；仍做 parent check、
写回和终检。`dune-build` 是公共命令名，实际使用当前 workspace 选择的 Dune 或 Make。

每次命令实际退出后检查最终 JSON。执行 `next_actions` 中的当前动作；存在 `waiting_for` 时等待
对应 owner。Owner 已完成报告且停止写入时，用 claim response 或 waiting entry 给出的
`finalize_invocation` 接纳。命令未返回后续动作时调用一次 `step`，不要自行拼接下一阶段命令。
没有动作、运行中的 owner 或明确 blocker 的未完成任务会报告 `controller-no-progress`，不应无限轮询。

## 初始化

`init-run` 确定 C 文件、独立的 formal case stem、固定 `target_files`、case-lib policy、问题描述、
symexec profile 和 group 限额。当前映射为
`QCP_examples/<collection>/.../<input>.c` → `Rocq/examples/<collection>/.../<case>_*.v`。

库策略为 `present`（已有）、`create`（创建 seed）或 `absent`（保持不存在）；未显式指定时依据
当前 canonical lib 是否存在选择前两者。`--freeze-spec` 指定用户已提供的函数 spec；省略时由
annotation owner 编写 spec。用户意图不清楚时，先澄清问题或 spec 权限，再初始化。

## Annotation

Annotation owner 按角色技能从题意设计数学 spec、必要 predicate、最小 function spec 与 loop
invariant，并在当前 attempt 内修正 symexec 暴露的问题。它只修改交接允许的 C annotation、
active case lib 和报告/plan，不手改 generated 文件或证明 manual。

开发检查顺序是 `formal-case-lib-design` → `symexec` → `formal-case-lib`；最后一步仅在库存在时
执行。Generated 输出由 controller 在临时目录生成和验证后发布。一次 symexec 命令至多启动
一次 driver；失败诊断交 owner 处理，不因零字节输出自动重跑。

Owner 写 `completed` 并停止后，main 的 `finalize-delivery` 直接完成 annotation 接纳：验证 plan
及冻结 spec、从当前输入重新生成一次、检查 failed-VC/current-VC comparisons、编译 active lib、
保存 after history。成功才把任务设为 `accepted` 并进入依赖准备。

需要改冻结 spec 时，owner 在 notes 写明函数、原/新含义、理由与影响，停止修改并交 main 请求
用户批准。批准后在同一 attempt `unfreeze`；接纳成功时记录新的 baseline。该流程不更换 owner。

## VC checking

有 manual VC 时，controller 创建独立 VC-checking owner。数学工作仍遵循该角色技能：先做
廉价 top-level structural blocker scan，再对没有明确 blocker 的输入完成全量 split-first 分析、
proof mode 选择和 group plan；独立复核 annotation comparisons，不能把其 `resolved` 当作证明。

Canonical 文件只读。需要观察 goal 时，只在 handoff 的 debug manual 副本中增加 `Show.`，再执行
给定 `coq-debug`。Main 的 `finalize-delivery` 检查调试编辑边界、当前 manual 的 plan 覆盖与分组
限制；成功后创建 proving task。不会为清除 Show 重跑 symexec。

## Group proving

`vc-proving-preparing` 从当前 plan 与 canonical manual/lib 创建每组独立副本和 handoff。
Assignment、路径和候选由当前输入派生。Owner 可只读查找 handoff 指定的历史证明，自行决定
复用；脚本不预填 proof/helper 或自动改名。

按 plan 数组顺序、并发限额派发。Annotation retry 后，覆盖 comparison `current` 的 groups 先运行；
它们全部 accepted 才派剩余 groups。优先批出现 annotation gap 时停止扩大派发，等待已运行或
returned 交付处理完毕，再聚合实际 blocker 进入 annotation retry。

Group owner 只修改 assigned proof spans 及允许的 suffixed helpers。`group-development` 和
`coq-debug` 提供开发反馈；`finalize-delivery` 必须检查当前结构、proof mode、helper suffix、禁止
假设/命令，并编译 assigned-witness wrapper。其他组的未完成 witness 不阻止本组接纳。

所有必要 group accepted 后，`vc-proving-verify` 从当前副本机械合并，再执行 full parent check。
合并或 parent 失败使用 controller 给出的修复/重试动作；main 不替 owner 修证明或改 plan。

## 修复与重试

可修的报告或检查失败把同一任务恢复为 `prepared`，保留 owner 并增加 `repair_index`；main claim
其 append action 后交原 agent 继续。不要把同任务修复变成新的 round。

| 已确认的原因 | 后续行为 |
|---|---|
| Annotation 自己发现 annotation/spec/dependency gap | 同 attempt、同 owner 继续修复 |
| VC checking 的 annotation/spec/dependency gap | 按结构化 VC feedback 创建 annotation retry |
| VC checking 的 plan/report defect | 创建 VC-checking retry |
| Group annotation gap | 等待当前批次可安全结束，聚合 exact VCs 后 annotation retry |
| Group plan defect | 根据当前 groups 的终态派生 VC-checking retry |
| 工具或基础设施 blocker | 保留诊断，不从错误文字猜测数学缺口或擅自换轮 |
| 当前输入不可读、parent 失败等机械问题 | 只执行 controller 派生的明确恢复/重试动作 |

`retry-round` 必须匹配当前 action，且 running/returned owner 均已处理。新 annotation attempt 带上
历史 `failed_vcs`，复制必要设计说明并重新填写 comparisons；所有实际旧缺口解决后才能交付。
模型写的 spec 可直接修，冻结用户 spec 仍需上述确认。

## 写回与终检

Parent 成功后 `final_candidate` 只记录 proving round。`final-apply` 重新读取该 round 的当前
candidate，编译最新候选并检查写入边界，再保存 original/candidate bytes 并发布。
`final-check` 检查实际 main-root 文件、独立 symexec replay、manual/VC 与 lib 边界、冻结 spec、Rocq 编译和
精确副产物清理。全部通过才进入 `done`。

失败或中断按当前 publication 记录恢复；发现外部新内容时保留备份并报告冲突，不能静默覆盖。
用户暂停只改变 control 与 signal，任务事实保持原样；明确恢复后重新派生动作。Acceptance 中断
留下的 `returned` 任务重新 finalize，不需要 owner 再次证明自己已经停止写入。
