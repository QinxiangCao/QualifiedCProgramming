# Group 命令与检查

## 一、唯一入口

只使用当前 `group_worker_input.md` 渲染的 exact argv 和 cwd，不从文件名、manifest、repository build
metadata 或历史命令推导。group-worker 可执行的 Rocq 外部入口只有：

- `controller.py coq-debug`
- `controller.py coq-check --target-kind group-development`
- `controller.py coq-check --target-kind group-check`

main agent 在 worker 启动前执行 `claim-attempt`，在 worker 停止写入后执行交接绑定的 `finalize-delivery`。group-worker 不自行运行或重建 claim/finalize，不调用 `step`、merge、parent verify、annotation feedback/retry 或 controller 任何其他 action。

命令必须原样执行。优先直接调用系统终端；若当前运行时仅通过 `functions.exec` 暴露终端操作，允许透明桥接：每个 cell 只 `await` 一次 `tools.exec_command` 来启动命令，或只调用一次 `tools.write_stdin` 来续接同一 live session（也可使用运行时为同一终端操作公布的规范化等价名称），并仅转发结果。启动时原样传入完整命令/argv、全部参数和 cwd，续接时保留同一 session 标识；不得把 argv 序列化为 shell 字符串、重新解析命令或增添引号。禁止：

- 在桥接 cell 中调用第二个工具、构造、修改、串联、并行或解释命令；
- 其他 JavaScript/Python 编排；
- 自建 shell/PowerShell/Python 脚本；
- 另一层 `uv run`；
- `sh -c`、管道、命令替换或后台进程；
- 直接调用 `coq_tooling.py`；
- 直接调用 `coqc`、`coqtop`、`coqc -o`、Dune 或 Rocq MCP；
- 从 repository build metadata 推导另一条命令；
- 自行补 cwd、flags、overlay 或 build path。

保留并继续等待任何外层 cell 和内层进程/会话标识，直到实际命令退出；透明桥接若返回仍在运行的 `functions.exec` cell，只用 `functions.wait` 恢复同一 cell，直到其中唯一一次终端操作返回。空输出、首次让出与 `Script completed` 不表示 controller 或 Rocq 已结束。只有退出码为 0，且 controller JSON 的 `status` 为 `passed`，检查才通过。

## 二、目录与 overlay

controller 已把 state、accepted plan、base manifest 和 group manifest 的本组结果渲染到交接，并在执行命令时派生：

- copied manual 到正式 manual relative path 的 overlay；
- 交接提供 `group_worker_lib` 时，它到 `formal_case_lib` relative path 的 overlay；
- exact build：`_coq_builds/<round>/<group>/src`；
- development build：同 group 下独立的增量目录；
- group-check wrapper 和 assigned witnesses；
- 唯一 debug script 路径。

group directory 只含 copied manual 与交接已提供的可选 `group_worker_lib`。`group_worker_lib` missing 时不创建 lib overlay，也不新增 helper/import。`public_helper_snapshot.txt` 不是 active lib，不作为 overlay，也不得 import。

controller 在创建、清理和写入 build 前拒绝 symlink、junction、reparse point 与非普通子项，并使用同目录不可预测临时文件加原子替换，避免输出被导向 run 外。

## 三、共同检查

development、exact 和 finalize 后的强制 validation 共用同一结构检查。每次都重验：

- current version；
- accepted plan；
- base manifest、group manifest 与 seed 封存；
- frozen public snapshot 与 reuse source digest；
- manual declaration order 和 statement token；
- assigned 与 unassigned proof token；
- `LLM_pre_process` split block；
- helper suffix、seed、import 与禁用规则；
- copied formal 中无 `Admitted.`、额外 `Axiom` 或禁用 lemma；
- formal 文件是否仍位于固定目录且未漂移。

注释、空白、CRLF/LF、行尾空白和 EOF 换行不参与 token 比较。

### Development 检查

`group-development` 只在本组可编辑 proof spans 允许临时 `Abort.`，不要求最终 proof completeness 或路线连接。它以增量方式编译 copied manual，用于证明搜索反馈，不能支持 `completed` 或 controller 接纳。

### Exact 检查

exact `group-check` 额外要求：

- 全部 assigned top-level VC 完成；
- 全部 aggressive split goals 完成；
- `LLM_pre_process` split blocks 保持 `Proof. Abort.`；
- top-level proof 使用 accepted `proof_mode`；
- 固定 group wrapper 的 Rocq 检查通过。

group-worker 对 aggressive top-level VC 只使用 `Goal_apply` 应用 split lemmas，但该证明原则不做 tactic 文本检查。

### Finalize 后的强制 validation

main agent 在 worker 停止写文件后执行 `finalize-delivery`。controller 先封存 `group_worker_report.json`、copied manual 和适用时的 `group_worker_lib`，再对同一 bytes 执行与报告终态匹配的强制 validation，并在检查前后重新比较封存：

- `status: completed` 必须通过完整结构、proof completeness、route 和 Rocq 检查，成功才把 group 置为 accepted。
- `blocker.failure_class: annotation-gap` 必须通过五字段 blocker 合同、witness/location 可追踪性、固定写入边界、statement/unassigned/mode 保护、helper/import/safety 和 seal 检查。缺口导致的 assigned proof 未完成不伪装成 `completed`，也不要求该终态通过本不可证的完整 group Rocq 目标；controller 封存为结构合法、可追踪且可供后续轮次条件式复用的 blocked 终态。
- 其他 blocker 继续按各自现有的结构检查、原地修复、重试耗尽或终止语义处理，不因 `annotation-gap` 汇总机制改变。

这是唯一强制 group validation。worker 的 development/exact 结果不写入最终报告，也不替代 controller 接纳或 blocked 封存结论。若 validation 只返回报告合同修复，本组 formal seal 保持不变，同 owner 只修报告并重跑原 finalize；不得借此修改 proof/lib。

## 四、固定 selected dependency 与 current build

accepted annotation 后，controller 已用 exact goal-check target 完成一次 `dune-build` action，并按 `_build` directory 判定封存 Dune 或 Makefile snapshot。group-local build只做以下工作：

1. 重验 snapshot、dependency source/artifact、selected configuration 与适用时的 run Makefile digests；
2. 把 persisted 五个 current case identities 中实际可达的 source，以及本组 overlay，stage 到 fixed local build；
3. 按 snapshot 中固定的 current edges 编译 current modules；
4. 从 selected base（Dune `_build/default` 或 Makefile main-root `Rocq/`）的绝对 `-R/-Q` mapping 读取 snapshot-bound dependency `.vo`；
5. 把 dependency artifact digest 绑定进 current cache 与 debug/reuse seal。

worker 不分析依赖、不提供 target、不运行 Dune、Make 或 `coqdep`。proof-time source 可以继续使用 snapshot 内已有的 project import和 Rocq installed standard-library import；新增 snapshot 外 project import 返回 mode-specific dependency-not-prepared failure，由后续 annotation retry形成新 accepted source与新 snapshot。本 group 不能动态扩展 dependency version。

current ownership 只来自 persisted case identity，不从 C stem、同目录前缀、helper 名或 import 推断。同目录其他程序/异名 lib 只有在 snapshot closure 中才可读取。每个 current dependency 在 consumer 编译或 debug 前必须已有本 build local `.vo`。

development 与强制检查共用 run-local current 前置产物缓存。缓存按 source、fixed current edges、工具、配置、flags 和 accepted dependency digest 寻址；删除、损坏或未命中只会从 source 重编 current 前置模块。强制检查的最终 target 始终实际运行。

以下情况必须给出精确失败，不能回退到整库 target、在 check 内编译 dependency source 或使用 source-tree 旧 current `.vo`：

- accepted dependency source/artifact/configuration 漂移；
- snapshot 外 project import；
- current edge、source 或 local artifact 不一致；
- 动态 `Load` 或 load-path 命令；
- 路径、mapping 或构建计划冲突。

## 五、超时与进程

一次 `coq-check` 或 `coq-debug` 中由 controller 启动的所有子进程共享 1800 秒截止时间。snapshot 校验和 staging 已用时间会从下一次启动的剩余时间扣除。

controller 把工具放进独立 process group；超时时终止整组，并保证输出读取有界。worker 不得绕过这一限制启动 raw 进程，也不得构造无上限替代命令。
