---
name: final-check
description: 由 main agent 在 final-apply 后确认 root generated/manual/formal_case_lib 与 accepted proving_merged_lib、versions 和 reports 一致。
---

# Final Check

本 skill 只由 main agent 使用，不启动 subagent。

## 文档

- `docs/final-check-guide.md`：final-apply、freshness、fixed Coq、manual/三级 lib/forbidden/cleanup。
- `../verification-orchestrator/docs/path-configuration.md`：freshness与 final Coq paths。

## 完成要求

- formal manual/`formal_case_lib` 只从 controller accepted proving_merged directory采用；`formal_case_lib` digest 等于 `proving_merged_lib`。
- scripted freshness symexec 输出到 report temp，不覆盖 proved manual；raw refresh manual 由 controller diagnostics split 后只比较 cleaned witness names/statements。
- main-root scripted full goal check passed，build files只在 run `_coq_builds`。
- manual/`formal_case_lib` 无 `Admitted.`、extra `Axiom`、forbidden lemma；manual只含 target witness proofs。
- helpers可追踪到 `group_worker_lib` reports与 `proving_merged_result.json`。
- controller 删除检查前旧 Coq 副产物并在检查后重扫；正式路径无新产生或无法删除的副产物，cleanup evidence 保持 compact。
- final-check 失败且 rollback 成功后回到 `final-candidate-apply`，必须重新 final-apply；rollback 失败时停止自动恢复。controller state/log记录 final result。
