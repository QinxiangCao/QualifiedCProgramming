# Controller 公共 CLI

```text
<python> <scripts>/verification-orchestrator/controller.py --main-root <root> <command> ...
```

要求 Python 恰为 3.12。首次可用仓库的 `uv run --frozen --python 3.12 python`；运行中的结构化
invocation 已提供绝对解释器与脚本路径。`--main-root` 默认 cwd，运行 action 时保留给定值。
除 `init-run`、`validate-artifact` 外，所有命令要求 `--run <run-id>`。

## 初始化

```text
init-run --case <formal-stem> --target-c-file <C-path>
```

`--case` 是合法 Rocq identifier，与 C 文件名无关。C 文件可为绝对路径或 main-root-relative 路径，
必须位于 `QCP_examples/<collection>/...`。其余选项：

| 选项 | 含义 |
|---|---|
| `--formal-case-lib-policy present\|create\|absent` | 已有库、创建 seed 或保持缺失；默认按当前文件选择 |
| `--freeze-spec <function>` | 冻结用户提供的 spec；可重复或逗号分隔，省略表示由 annotation owner 编写 |
| `--max-witnesses-per-group <n>` | 正整数，默认 12 |
| `--max-parallel-group-workers <n>` | 正整数，默认 5 |
| `--symexec-profile standard\|recursive-large` | 选择现有 symexec 预算，默认 standard |
| `--problem-statement` / `--problem-statement-file` | 题意文本或 UTF-8 文件 |
| `--target-function` / `--expected-behavior` / `--input-output-contract` | 当前问题约束 |
| `--spec-hint` / `--preferred-hidden-property` / `--forbidden-pattern` / `--reference-case-hint` | 可重复的 owner 提示 |
| `--timestamp <YYYYMMDDhhmmss>` | 可选的 14 位 run 时间标识 |

## 当前 18 个命令

| 命令 | 除 `--run` 外的参数 | 作用 |
|---|---|---|
| `init-run` | 见上 | 创建 schema 4 run |
| `step` | 无 | 读取当前事实并返回 actions、waiting 和 blockers |
| `claim-attempt` | `--next-action --owner` | 领取当前 owner action，返回 handoff 与 finalize invocation |
| `finalize-delivery` | `--attempt --owner` | 记录 owner 已停止，直接完成该角色全部接纳检查 |
| `retry-round` | `--phase annotation\|vc-checking --reason --previous-attempt` | 执行当前 action 指定的重试 |
| `unfreeze` | `--round` | 用户批准后解除当前 annotation 的 spec baseline 约束 |
| `dune-build` | 无 | 当前 native backend 准备依赖，再进入 VC checking 或空 proving |
| `vc-proving-preparing` | `--round` | 创建当前 group copies 和 handoffs |
| `vc-proving-verify` | `--round` | 读取当前 groups、机械合并并执行 parent check |
| `symexec` | `--round` | Annotation owner 在当前任务生成并发布输出 |
| `coq-check` | `--round --target-kind`，group 类型另需 `--group` | 开发/精确检查 |
| `coq-debug` | `--round`，group owner 另需 `--group` | 检查已授权的 debug script/copy |
| `final-apply` | 无 | 重查最新候选并可恢复地发布 |
| `final-check` | 无 | 检查实际文件、独立 replay 与清理；通过后 done |
| `pause-run` | `--reason` | 暂停 run，保留任务事实 |
| `cancel-action` | `--action --reason` | 验证当前/已领取 action id 后暂停 run |
| `resume-run` | 无 | 明确恢复后重新派生动作 |
| `validate-artifact` | `--kind --path`，不需 `--run` | 用运行时 validator 校验指定文件 |

`coq-check --target-kind` 仅支持 `formal-case-lib-design`、`formal-case-lib`、`group-development`、
`group-check`。`validate-artifact --kind` 仅支持 `agent-report`、`group-worker-report`、
`annotation-plan`、`controller-state`、`run-log`。

## 使用约定

执行 controller 返回的 invocation，不从这张表自行推断当前允许的阶段。
Owner action 先 claim；main 在 owner 停止写入后 finalize。`returned` 可重做 finalize 继续中断的
接纳；可修错误回到同 owner 的 prepared action。

结果类型随命令而异：工具检查要同时成功退出且 JSON `passed`；claim 返回 `claimed` 或
`already-claimed`；接纳返回 `accepted`、repair 或 blocker；`step` 返回 run 状态及当前 actions。
不要把 exit code 0、owner 的 `completed` 或单个 `valid` 报告当作整个 run 已完成。

当前接口没有独立 annotation/VC acceptance 命令。旧 schema run 不迁移，也不应手改 schema
后继续；使用原代码恢复或初始化新 run。用户暂停后只有明确恢复授权才能执行 `resume-run`。
