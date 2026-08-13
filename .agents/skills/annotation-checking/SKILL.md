---
name: annotation-checking
description: Run 内唯一 annotation owner 已形成首次候选或按 retry 反馈修正候选后使用；由同一 annotation agent 检查 main root 当前 C annotation、已存在的 formal_case_lib、generated 结果和汇总 blocker 覆盖情况，在允许边界内循环返修，并决定候选是否可以交回 main agent finalize。
---

# Annotation 检查

本 skill 只在当前 annotation owner 的同一工作中使用，不创建 checking agent。它检查并反馈当前候选，不决定 controller 是否接纳，也不读取根 `AGENTS.md`、orchestrator、其他角色 skill 或推断后续证明动作。

## 必须阅读

1. 完整读取 [候选检查流程](workflows/annotation-checking.md) 与 [规范质量检查表](docs/spec-quality-checklist.md)。
2. 重新读取 [annotation-filling](../annotation-filling/SKILL.md) 与其 [workflow](../annotation-filling/workflows/annotation-filling.md)；所有修正、命令和交付仍受 annotation owner 的共同写入边界约束。
3. 按候选实际结构查阅 `annotation-filling` 直接导航的谓词、普通 `Assert`、数组/字符串、分支控制或纯命题知识文档。

流程细节以 workflow 为准。通过只表示当前 owner 可以写完成报告并停止写入；它不替代 controller 的 finalize 或接纳检查。
