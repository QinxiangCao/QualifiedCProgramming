---
name: group-worker-proving
description: group-worker 领取 controller 已 claim 的 group_worker_input.md 或收到同 owner 的 append-group-worker 后使用；handoff 给出上一 proving round 时先搜索相关旧 proof/helper并可选记录简短 proof_reuse.md，再在固定 group directory 中证明 assigned witnesses，修改 copied manual 与可选 group_worker_lib，并交付 completed 或带结构化 vcs 的 blocker。
---

# Group Worker 证明

## 角色边界

只以当前 claim/handoff、本 skill 及其链接文档为依据。不读根 `AGENTS.md`、orchestrator 或其他角色 skill，不依赖 parent transcript，不读取或等待 sibling group，不调度其他 group，不执行 merge、parent verify 或 annotation retry。

这些读取约束用于避免把非当前内容当作证明输入；偶然多读文件本身不构成 blocker。只要没有越界写入、没有依赖 current-round sibling 输出，并且最终 proof 通过本组 controller validation，就继续当前 delivery。

按 controller 已验证的 `proof_mode` 完成本组 top-level VC 和适用的 split goals，在交接指定的固定副本中维护 proof/helper，使用交接给出的命令做可选预检，最后停止写入并交付报告，等待 main agent 调用 `finalize-delivery` 封存和验证。

handoff 给出上一 proving round 时，先按 current witness/helper 名跨该轮各组 copied manual/lib搜索，只读取匹配候选的 declaration/proof block，再判断直接复用、修改后复用还是不复用。不要逐份通读相同的完整 manual副本。可选的 `proof_reuse.md` 只记录这一判断；缺失或为空不影响 finalize，controller 不做旧证明匹配，也不解析该文件。

诊断出 annotation/spec 缺口时，该缺口是本 group 的终态结果：停止在本组副本中追加越界修正，写入完整 blocker；`vcs` 逐项给出 sealed manual 中的精确 `name`、`parent` 和 `annotation_location`，`message` 只解释已有 premise 与缺失结论。本 worker 不据此判断、停止或推进任何其他 group 或 parent 阶段。

## 需要阅读

- 始终完整阅读 [执行流程](workflows/group-worker-proving.md)、[命令与检查](workflows/commands-and-checks.md) 和 [必须遵循的禁用 lemma 原则](docs/forbidden-lemma.md)。
- 开始 manual VC 证明前阅读 [完整分离逻辑证明方法](docs/separation-logic-whole-proof-tactics.md)。
- 本组包含精化目标时阅读 [精化证明方法](docs/refinement-proof-tactics.md)。
- 本组使用顺序性、边界、sum 或其他纯命题 predicate 时阅读 [纯命题证明方法](docs/pure-proposition-proof-patterns.md)。
- 确实需要查找类似证明时才阅读 [参考案例](docs/reference-cases.md)。
