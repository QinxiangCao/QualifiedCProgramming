# Final Check 指南

本文件给 main agent 使用。final-check 不开启 subagent。

## final-candidate-apply

main agent 必须先执行 `final-candidate-apply`：

- 从 controller accepted final candidate 复制最终 `.c`、generated files、`*_proof_manual.v` 和 `case_lib` 到 main worktree。
- apply 来源必须与 `run_logs.json` 最新 state snapshot 中当前 accepted `vc-proving-preparing` / `group_merged_result.json` final candidate 一致。
- apply 前在 `<report-root>/final-check/backup/` 记录 touched formal files 的 backup metadata。
- apply 后记录当前 `source_version`、`source_goal_version` 和 copied file digests。
- QCP / `coqc_check` / structure audit 失败时，按 backup rollback，并在 `run_logs.json` state snapshot / blockers 中记录失败命令和 rollback result。

不得从 group worktree、stale round worktree 或未被 controller 记录为 final candidate 的目录直接复制 formal files。

## Symbolic execution freshness 检查

final-check 必须确认 generated files 来自当前 main worktree 目标 `.c`，并与已采用的 `case_lib` / manual proofs 一致。

`QCP_examples/LLM_bench` case 使用 `QCP_demos_LLM` 公共头文件时，symbolic execution 必须带：

```bash
-IQCP_examples/QCP_demos_LLM/
-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM
```

不得在 final-check 中把源码 include 改成相对路径来规避 include path 配置。

freshness refresh 必须输出到 report root 下的 temp directory，例如：

```text
<report-root>/final-check/symexec-refresh/
```

然后比对 temp generated files 与 main worktree 已采用 files：

- `*_goal.v`
- `*_proof_auto.v`
- `*_proof_manual.v`
- `*_goal_check.v`

`case_lib` 不由 symbolic execution 重写。temp `*_proof_manual.v` skeleton 只用于比对 witness names、witness statements 和 skeleton freshness；不得复制回 main worktree 覆盖已完成 proof bodies。

若 temp witness statements 与 main worktree manual proofs 不一致，或 generated goal/check/auto 文件不一致，记录 blocker 并回到 `vc-proving-preparing` / group-worker 或 `annotation`。

## Fixed `coqc_check`

final-check 的 canonical batch check 使用 main worktree 的固定 Coq helper：

```bash
python3 <main-worktree-root>/.agents/skills/vc-proving/scripts/coq_tooling.py check \
  --workspace-root <main-worktree-root> \
  --build-workspace <run-root>/_coq_builds/final-check/src \
  --target-file SeparationLogic/examples/LLM_bench/Algorithms/<case>/<case>_goal_check.v \
  --target-kind check \
  --source-goal-version <source_goal_version>
```

不得手写 Coq flags、使用 `coqc -o`、调用 Dune、调用 Rocq MCP 或 `_CoqProject` derived command。失败的 fixed command 就是 evidence，不能作为切换工具或参数的授权。

helper 会把 formal source `.v` 文件 mirror 到 `--build-workspace` 后运行 `coqc`。`.vo`、`.vos`、`.vok`、`.glob` 和 `.aux` 只能出现在 build workspace 下，不得写入 main formal path。

`verification_result.final_check.coqc_check` 必须记录 argv、cwd、Coq version、fixed flags hash、target file、target kind、`source_goal_version`、source digests、return code、stdout/stderr tails 和 first diagnostic。无法运行时写 `skipped` 或 `failed`，不得写成 `passed`。

## Manual proof 和 `case_lib` review

必须检查：

- `*_proof_manual.v` 不含 `Admitted.`、extra `Axiom`、顶层 `Definition`、`Fixpoint`、`Inductive`、`Notation` 或 helper lemma。
- `*_proof_manual.v` 只包含当前 case 的 manual witness theorem proofs。
- `case_lib` 不含 `Admitted.`、extra `Axiom` 或当前 case generated artifact 的 `SimpleC.EE.*` import。
- `case_lib` 中新增 helper declarations 能追踪到 vc-proving parent verify 的 merge record。
- `*_proof_manual.v` 和 `case_lib` 不使用 `.agents/skills/verification-orchestrator/docs/forbidden-lemma.md` 列出的 forbidden lemmas。
- main worktree diff 只包含本 case accepted files。

建议先文本扫描：

```bash
rg -n '\bAdmitted\.|\bAxiom\b' path/to/case_proof_manual.v path/to/case_lib.v
```

再扫描 forbidden lemma 列表中的 lemma 名称。命中时 final-check 失败，并回到 `vc-proving`。

## Cleanup 范围

可清理：

- 本 run 创建的 annotation / vc-checking round worktree。
- 本 run 创建的 `vc-proving-preparing` 普通 container 目录。
- 本 run 创建的 group worktree。
- report temp directories。
- 当前 case 对应的 Coq `.aux` / `.glob` / `.vo` / `.vos` / `.vok` 等编译副产物，前提是它们不是正式交付。
- Python/test 临时目录。

不得删除：

- 目标 `.c`
- `*_goal.v`
- `*_proof_auto.v`
- `*_proof_manual.v`
- `*_goal_check.v`
- `case_lib`
- run level / round level / group-worker level 的正式 JSON/text handoff files，除非用户明确要求清理整个 run 记录。

只有 freshness、fixed `coqc_check`、manual proof structure、`case_lib` contract、merge record 和 cleanup 全部通过后，main agent 才能进入 `done`。
