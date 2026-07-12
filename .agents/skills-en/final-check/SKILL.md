---
name: final-check
description: 由 main agent 在 final-candidate-apply 后执行最终检查，确认 generated files、manual proofs、case_lib 和 main worktree 状态一致。
---

# Final Check

本 skill 只由 main agent 使用，不启动 subagent。

## 文档

- `docs/final-check-guide.md`：final-candidate-apply、symbolic execution freshness、fixed `coqc_check`、manual proof / `case_lib` review 和 cleanup。

## 完成要求

- main worktree 只从 controller accepted final candidate 采用正式文件；该 candidate 来自已通过 `vc-proving-verify` 的 `group_merged_result.json`。
- symbolic execution 到文件尾，且 generated files 与当前 main worktree 目标 `.c` 一致。
- main-path fixed `coqc_check` 通过。
- `*_proof_manual.v` 和 `case_lib` 不含 `Admitted.`、extra `Axiom` 或 forbidden lemma。
- `*_proof_manual.v` 只含当前 case 的 manual witness theorem proofs，没有 helper declarations 或 forbidden top-level declarations。
- `case_lib` contract 通过，新增 helper declarations 可追踪到 parent verify merge record。
- cleanup 只清理本 run 临时产物，不删除正式交付文件。
- `run_logs.json` 记录 final-check 结果。
