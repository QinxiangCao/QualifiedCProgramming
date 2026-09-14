---
name: annotation-designing
description: Controller 首次交付 annotation attempt 或追加失败 VC 时使用；由同一 annotation owner 从题意生成数学 spec，优先复用已有核心 predicate，填写最小 function spec 与 loop invariant，并在当前 attempt 内完成 symexec 修正。
---

# Annotation 设计与填写

一个 run 只使用一个 annotation owner。首次 attempt 与 retry 都由同一 owner 在 main root 中继续处理。

按以下顺序工作：

    题意
      -> 自然语言 spec
      -> Rocq spec
      -> C function spec
      -> loop invariant
      -> symexec

自然语言 spec、Rocq Spec 和 C Ensure 表达同一输出关系。题解、算法提示、循环状态、DP 转移和数据结构构造过程不进入顶层 spec。

写新 definition 前搜索当前依赖、canonical case lib 和公共库。Zlength、Znth、sublist、replace_Znth、Forall、Forall2、In、NoDup、Permutation、sum、已有单调性、最值、路径和数组 predicate 可以直接组合时，不再定义同义 predicate，也不为其组合结果逐层套 wrapper。题目语义或跨函数接口需要名称时只保留一层 case predicate，其他位置直接引用它。

Function spec 直接展开输入范围、元素范围和 overflow 条件；With 管理逻辑值，Require 管理入口条件和资源，Ensure 调用数学结果 predicate 并归还资源。

每个循环前写一条 Inv Assert，只包含当前数学进度、下一次执行需要的范围、仍存活的资源和必要的 @pre bridge。普通 Assert 只在 symbolic execution 无法得到下游必需状态时使用；可按需放在 if 前，不放在 return 或 Inv Assert 前。函数体不使用 by local、branch-control、普通 Inv、multi-inv 或 call where。

用户提供的 spec 保持不变。确实需要修改时，在 agent_output.md 写明函数、原因、修改内容和语义变化，交回 main；main 完成用户确认和 unfreeze 后，在同一 attempt 中继续。

## 必须阅读

1. 完整读取 [设计、填写与修正流程](workflows/annotation-designing.md)。
2. 完整读取 [Annotation 设计指南](docs/annotation-design-guide.md)、[QCP C Annotation 填写参考](docs/annotation-authoring-reference.md)、[Spec 与 Function Contract 知识规则](docs/spec-and-contract-knowledge.md) 与 [自检清单](docs/design-and-annotation-checklist.md)。新增知识规则只约束产物内容，不改变 workflow。
3. 涉及数组或字符串时读取 [数组与字符串](docs/array-string-guide.md)。
4. 涉及纯命题、有限量化或 witness 时读取 [纯命题 predicate](docs/pure-proposition-predicates.md)。
5. 需要普通 Assert 时读取 [普通 Assert 的放置](docs/semantic-assert-placement.md)。
6. 需要具体例子时读取 [精简 predicate 示例](docs/internal-predicate-examples.md)；二分答案或算法镜像只读取对应 examples。

严格遵循 workflow 的输入、写入边界、命令、retry、报告与 finalize-repair 合同。不要修改 proof manual，不写 proof。
