# Coq Tooling 规则

`coq_tooling.py` 是唯一 Coq feedback 和 verification 入口。

不得调用 raw `coqc`、`coqc -o`、Dune、Rocq MCP 或 `_CoqProject` derived command。

## Batch check 入口

使用 `coq_tooling.py check`。evidence 必须记录 fixed flags hash、argv、cwd、target file、target kind、return code、stdout/stderr tails 和 `source_goal_version`。

`coq_tooling.py check` 只把 `coqc` 返回 `-9` / `SIGKILL` 视为 transient failure 并重试；重试次数由 `COQC_TRANSIENT_RETRIES` 配置，默认 2 次。不要把 `SIGTERM`、`SIGINT`、`SIGSEGV`、`SIGBUS`、`SIGABRT` 或普通 proof failure 当作 transient retry。

## Debug 入口

使用 `coq_tooling.py debug` 获取固定 `coqtop -batch` feedback。debug evidence 不是 acceptance evidence。

## Group check evidence

group-worker final feedback 必须满足：

- `target_kind == "group-check"`
- target 位于 `.coq_group_checks/`
- `--workspace-root` 是 group worktree
- build workspace 是 group-unique `_coq_builds/<round>/<group>/src`
- `source_goal_version` 是当前版本

parent verify 合并 group results 后仍会运行 parent full check。
