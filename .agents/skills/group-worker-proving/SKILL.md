---
name: group-worker-proving
description: group-worker 领取 controller 已 claim 的 group_worker_input.md 或收到同 owner 的 append-group-worker 后使用；只在固定 group directory 中证明 assigned witnesses，修改交接给出的 copied manual 与可选 group_worker_lib，并交付 completed 或带完整 blocker 的终态报告。
---

# Group Worker 证明

## 角色边界

只以当前 claim/handoff、本 skill 及其链接文档为依据。不读根 `AGENTS.md`、orchestrator 或其他角色 skill，不依赖 parent transcript，不读取或等待 sibling group，不调度其他 group，不执行 merge、parent verify 或 annotation retry。

按 controller 已验证的 `proof_mode` 完成本组 top-level VC 和适用的 split goals，在交接指定的固定副本中维护 proof/helper，使用交接给出的命令做可选预检，最后停止写入并交付报告，等待 main agent 调用 `finalize-delivery` 封存和验证。

诊断出 annotation/spec 缺口时，该缺口是本 group 的终态结果：停止在本组副本中追加越界修正，写入可追踪的完整 blocker 并正常交付。本 worker 不据此判断、停止或推进任何其他 group 或 parent 阶段。

## 需要阅读

- 始终完整阅读 [执行流程](workflows/group-worker-proving.md)、[命令与检查](workflows/commands-and-checks.md) 和 [必须遵循的禁用 lemma 原则](docs/forbidden-lemma.md)。
- 开始 manual VC 证明前阅读 [完整分离逻辑证明方法](docs/separation-logic-whole-proof-tactics.md)。
- 本组包含精化目标时阅读 [精化证明方法](docs/refinement-proof-tactics.md)。
- 本组使用顺序性、边界、sum 或其他纯命题 predicate 时阅读 [纯命题证明方法](docs/pure-proposition-proof-patterns.md)。
- 确实需要查找类似证明时才阅读 [参考案例](docs/reference-cases.md)。
