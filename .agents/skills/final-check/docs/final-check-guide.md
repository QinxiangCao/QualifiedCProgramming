# Final Check 指南

本文件给 main agent 使用；final-check 不启动 subagent。

## final-apply

controller 只接受 `proving_merged_result.json.status == passed` 且 parent full scripted check passed 的 candidate。

final-apply：

- source必须位于 accepted `verification_runs/<run>/<round>/proving_merged/`。
- 只复制 merged manual与`proving_merged_lib`到 main root formal manual/`formal_case_lib`。
- target C/generated files已由 accepted annotation保留在 main root，不从group/merged directory复制。
- apply前在 `reports/<run>/final-check/backup/` 保存 touched files；失败或 final-check failed时 rollback。

不得直接从 group directory或 stale history/report采用文件。

## Symbolic execution freshness

controller 内部使用 `symexec_tooling.py`，output root固定为：

```text
reports/<run>/final-check/symexec-refresh/
```

helper自动拼 driver、cwd、canonical include/SLP、logic/generated paths。fresh goal/auto/check与main root逐文件比较；raw fresh manual先在 refresh directory 内执行与 annotation acceptance 相同的 diagnostics split，fresh cleaned manual只比较 witness names/statements，不覆盖proved bodies。refresh diagnostics与snapshot只属于本次 freshness evidence，不写回main root。

current target C digest还必须等于 accepted annotation `source_version` 中记录的 target C；final applied `formal_case_lib`预期不同于 annotation seed，因此不对它做错误的整份 source-version等值比较。

## Fixed Coq check

controller 内部使用 `coq_tooling.py` 的 fixed check：workspace是main root，build在`verification_runs/<run>/_coq_builds/final-check/src`，target是root-relative goal check，target kind是`check`，version是current `source_goal_version`。`coqc`路径来自`SeparationLogic/CONFIGURE`和Makefile的`COQBIN`/`SUF`约定；与其他run和阶段一致，check从main root全量make产物复用Makefile全部load path的基础`.vo`，不按源码digest、Coq版本或flags建cache且不重编译基础库。current target case的lib/goal/auto/manual/check五个module排除旧产物并从applied source重新编译。main agent 不直接调用 internal helper。

不得手写Coq flags/raw commands。controller state只保留 status、version、return code与首个失败 diagnostic等必要摘要；需要完整反馈时原样重跑同一 controller check。

## Manual 与三级 lib review

- manual无`Admitted.`/`Abort.`/extra `Axiom`/helper/forbidden top-level declaration。
- manual witness list与`source_goal_version.target_witnesses`完全一致。
- `formal_case_lib`无`Admitted.`/extra `Axiom`/current generated artifact import。
- `formal_case_lib` digest等于accepted `proving_merged_lib`。
- merged helpers可追踪到`group_worker_lib` reports与`proving_merged_result.json`。
- manual/`formal_case_lib`不使用 forbidden lemma list。

## Cleanup

final-check开始时，controller只删除current target case五个formal modules及current run非`_coq_builds`区域中的旧`.vo/.vos/.vok/.glob/.aux`并记录删除数量；前置全量make产生的基础`.vo`必须保留。freshness、fixed Coq及结构检查完成后controller再次扫描同一target/run边界；新产生或无法删除的target副产物使cleanup失败。state/output只保存删除数、错误数、残留数以及首个错误或残留路径，不保存完整路径列表。

current target case的新Coq副产物只允许位于current run `_coq_builds`；main root基础库`.vo`是允许且必需的条件信任输入。agent不手工执行cleanup。controller不得删除正式交付文件、基础`.vo`、controller state、run log、任何`annotation-attempts/annotation-attemptN` handoff/report、formal annotation history、round/group reports或merge record。

## Failure recovery

任一final-check项失败都rollback final-apply。rollback成功后phase回到`final-candidate-apply`，main agent调用`step`并执行返回的`final-apply`，之后才能再次final-check；不得对rolled-back root直接重跑final-check。rollback失败时controller保留blocker且不返回新的apply/check action。

所有 freshness/fixed check/structure/lib/forbidden/cleanup项通过后才能写done；否则记录blocker并rollback final apply。
