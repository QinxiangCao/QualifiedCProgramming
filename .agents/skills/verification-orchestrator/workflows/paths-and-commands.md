# 路径与命令

## 1. Controller 入口

唯一公共入口：

```text
<python> .agents/scripts/verification-orchestrator/controller.py --main-root <root> <command> ...
```

main 只执行 action 中的结构化 `invocation`，不从本文拼 argv。Owner 只执行 handoff `Commands`。不要直接调用内部 Python module、raw symexec、raw Coq、Dune 或 Make。

每条命令使用给定 cwd/argv；运行中的 terminal session 必须续接到真实退出。退出码 0 和最终 JSON success status 缺一不可。

整个 workflow 中 controller 启动的 Coq/build 进程统一使用 900 秒上限，包括 annotation、VC checking、group、parent verify、final check 和 dependency preparation。进程在独立 process group 中运行；超时后 controller 显式终止整组，仍未退出就强制 kill，不能只返回 timeout 状态。

## 2. 固定 roots

```text
<root>/verification_runs/<run>/
<root>/reports/<run>/
```

`target_files` 固定 C、formal directory、case lib、goal、auto、manual、goal-check、case name 和 active theory。C stem 不一定等于 case stem；始终使用 state/action 的 exact path。

Annotation source 在 main root；`before/after` history 是 controller-owned seal。VC checking 只可临时修改 main-root manual 中的 `Show.`。Group worker 只写固定 group copy。Final apply 前不得把 group/merged candidate 手工复制到 main root。

## 3. Annotation commands

Handoff 顺序：

```text
coq-check --target-kind formal-case-lib-design
symexec
coq-check --target-kind formal-case-lib       # active lib
```

Agent 编写的 spec 可与内部 annotation 和 case lib 在当前 attempt 中共同修改，每次修改后可重跑 `formal-case-lib-design` 与 symexec。用户 spec 需要修改时，owner 先停止并把方案交给 main；用户确认后 main 执行 `unfreeze --run <run> --round <round>`，再把方案交回同一 owner。`unfreeze` 不出现在 owner handoff commands 中。

`symexec` 事务化删除并重建 exact generated roles。Owner 在 retry symexec 后读取当前 manual 并填写 VC comparisons；proof manual 永远只读。

## 4. VC checking commands

Owner 可在 current manual 临时插入 `Show.`，每次有用修改后执行 handoff 的：

```text
coq-debug --run <run> --round <vc-checking-round>
```

交付成功后 controller 运行 `vc-checking-check-round`，重新 symexec 并 seal clean manual/group plan。

## 5. Group commands

每组 handoff 给出 fixed directory、copied manual、可选 group lib、report paths 和两条 controller command：

```text
coq-check --target-kind group-development --group <id>
coq-check --target-kind group-check --group <id>
```

Worker 可反复运行 development check；controller acceptance 总会运行 exact group check。不要运行 sibling group command，不要把 group path替换为 main-root path。

若上一 round 存在，每个实际领取任务的 worker 在 handed-off previous directory 中按 current witness/helper搜索，只读取候选 proof block，不逐份通读完整 manual。可按需写 `proof_reuse.md`；该文件缺失或为空均可，controller 不解析也不据此阻断 finalize。当前 manual/plan 始终为准。

## 6. Main-owned actions

main 只使用 action 自带 invocation：

- `retry-round` 创建 annotation/vc-checking retry；
- `unfreeze` 在用户确认后允许当前 annotation attempt 修改用户 spec；
- `annotation-check-round`、`vc-checking-check-round` 接纳 owner 交付；
- `dune-build` seal dependency snapshot；
- `vc-proving-preparing` 建 group copies、交接上一 round并调度；
- `vc-proving-verify` merge 与 parent check；
- `final-apply`、`final-check` 写回与终检；
- `pause-run`、`cancel-action`、`resume-run` 控制运行。

## 7. Seal 与删除边界

Controller 在读取、写入、删除、复用或验证前重算目标路径并拒绝 alias/symlink/跨 run/错 round。Agent 不删除 run/report tree，不修改 manifests、state、history 或 seals。

Final check 成功时 controller 负责清理；失败时按 action 修复或回滚。
