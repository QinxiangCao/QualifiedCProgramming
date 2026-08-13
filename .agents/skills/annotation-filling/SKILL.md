---
name: annotation-filling
description: Controller 为某个 run 首次交付 annotation attempt，或把 annotation-check、parent/group 汇总出的 annotation 缺口追加给同一 owner 时使用；由 run 内唯一且持续复用的 annotation agent 在 main root 补充或修正目标 C annotation，维护已存在的 formal_case_lib 数学规范，并在同一工作中调用 annotation-checking。
---

# Annotation 填充

你是本 run 唯一的 annotation owner。首次 attempt 与所有 retry 都复用当前 agent target；不要创建替代 owner，不要读取根 `AGENTS.md`、orchestrator 或其他角色 skill，也不要推断、启动或修复后续证明阶段。

## 必须阅读

1. 完整读取 [填写与修正流程](workflows/annotation-filling.md)。
2. 在同一工作中完整读取 [annotation-checking](../annotation-checking/SKILL.md) 与其 [workflow](../annotation-checking/workflows/annotation-checking.md)，并按其要求完成检查循环。
3. 阅读 [Annotation 填写指南](docs/annotation-guide.md)、[谓词优先设计](docs/predicate-first-annotation.md)、[普通 Assert 的位置](docs/semantic-assert-placement.md) 与 [QCP 参考](docs/qcp-reference-guide.md)。
4. 任务涉及对应结构时，再读取 [数组与字符串](docs/array-string-guide.md)、[分支控制](docs/branch-control-annotation.md) 或 [纯命题谓词](docs/pure-proposition-predicates.md)。
5. 若本 attempt 的 controller 交接明确指定本 skill 内的正确/错误示例，读取被指定的文件；不要自行扩展到其他角色文档。

详细的输入解释、写入边界、命令合同、汇总反馈处理、检查循环、报告与 finalize 修正规则均以 workflow 为准。
