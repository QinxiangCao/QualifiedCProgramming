# 路径与命令

公共入口为当前代码的 `verification-orchestrator/controller.py`。首次使用：

```sh
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py --main-root <root> <command> ...
```

运行中 action 和 handoff Commands 使用 `{ "argv": [...], "cwd": "..." }`。保持解释器、参数和
cwd；终端支持 argv 时直接传数组，仅支持字符串时按实际 shell 逐参数引用。保留工具/session
句柄到实际退出，检查退出码和该命令的 JSON 结果。不得追加 raw Coq/symexec/Dune/Make 参数，
或调用内部模块来跳过 controller。

脚本路径取自正在运行的代码，workspace 由 `--main-root` 确定，两者不需要处于同一 checkout。
C 相对路径依据 main root 解释。`target_files` 固定所有 canonical 文件，C stem 与 formal stem
可以不同；collection 和任意深度子目录仍须能组成合法 Rocq logical path。

## 普通文件与发布

JSON 中仓库相对路径使用 `/`，保留 Coq identity 大小写。文件操作使用 Path；拒绝逃逸、symlink、
junction、reparse point 和非普通输入，先检查路径分量再规范化。C/strategy include 的 `..` 仅在
直接解析仍处于 `QCP_examples` 内时接受；歧义 include 交 owner 修正。

Generated/staging 文本使用 UTF-8/LF；original backup 保存原 bytes。正式替换使用目标目录内
临时文件，flush/fsync、关闭后 `os.replace`。Annotation 先在新目录生成，全部输出有效后发布；
失败不先删除 canonical manual。可选 manual 真正缺失时不创建占位文件。

Final publication 保留 original/candidate bytes。恢复时核对固定 role/path 和当前内容；外部新内容
不能被静默覆盖。遇文件占用保留原件和备份并报告实际错误。

## 依赖准备与 Rocq

Workspace 有 `_build` directory 时选 Dune，否则选 Make。Dune 用 native rules 找依赖并 build base；
Make 用 coqdep 和临时 exact Makefile。统一 `dependency_plan.json` 仅保存 `build_mode`、`target`、
`case_anchor`、`dependencies`，current/base 从当前 case family 与图计算。

后端共用一条 stage→选择依赖→编译流程。每个检查读取当前文件并准备 native dependencies；
current 模块实际运行 coqc，base 使用 native incremental build。Staging 在内存规范化生成器
import 和 auto/manual overlap，只写变化内容；final prelude 比较复用相同 import 规范化。

Group wrapper 只要求 assigned witnesses，active case lib 即使未被 goal-check 引用也独立编译。
VC debug manual 和 group copies 以 overlay 进入 run 的 build 目录，canonical manual 保持只读。
合并后 parent 检查完整 goal-check，final apply 再检查最新候选。

## 工具预算和输出

一次 Coq check/debug 的依赖准备、等待和编译共享至多 900 秒。Dune workspace lock 串行化共享
依赖刷新，释放后组内编译继续并行；等待计入预算并响应取消。较长 native 命令向 stderr 报告
阶段与耗时，stdout 留给终态 JSON。

Symexec 使用初始化时选择的 profile；一条命令至多启动一次 driver。零字节或缺失必需输出是
失败，不自动启动第二次。Progress 是诊断，不能替代成功退出与完整输出检查。

零预算或已取消时不启动新进程；timeout/pause 清理独立进程组及后代，并限时回收输出。
Windows 不保证运行中部分 stdout/stderr；成功清理后保留最终输出，管道仍被脱离进程持有时
报告 `cleanup_incomplete`。用户明确恢复前不继续。

Final cleanup 只删除允许的生成副产物，并在遍历前跳过 `_coq_builds`；保留 source、报告、历史、
candidate 和 base 库产物。
