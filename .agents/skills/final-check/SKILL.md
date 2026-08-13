---
name: final-check
description: main agent 在 final-apply 写回 accepted proving_merged 后使用；确认 main root 的生成文件、manual、formal_case_lib、版本、合并结果与清理结果一致。
---

# 最终检查

## 何时调用

只由 main agent 在 controller 已完成 `final-apply` 后调用，不创建 subagent。终检失败并成功回滚后，必须先按 controller action 重新执行 `final-apply`，不能直接重跑终检。

首次公共入口由人类用根级 uv/Python 3.12 环境启动；这里的 `final-check` 只执行 controller action 中以已验证绝对 `sys.executable` 开头的完整 argv，不重新包 uv。

## 大概作用

通过 controller 复查来源封存、symbolic execution 新鲜度、Rocq 全量检查、manual 路线、三级 lib、禁用 lemma 与副产物清理；全部通过后才结束 run。

## 需要阅读

- [执行流程](workflows/final-check.md)
- [路径与命令](../verification-orchestrator/workflows/paths-and-commands.md)
- [Controller 公共接口](../verification-orchestrator/docs/controller-cli.md)

main 不需要读取 group-worker 或其他 subagent skill。禁用 lemma、证明结构和来源封存由 controller 机械检查；main 只执行 action 自带的完整 invocation。
