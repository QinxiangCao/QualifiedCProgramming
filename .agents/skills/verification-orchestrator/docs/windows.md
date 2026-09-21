# Windows 运行规则

按仓库 [Windows setup](../../../../docs/windows-setup.md) 配置原生 PowerShell、uv/Python 3.12、
Coq 和所选构建工具。保留 setup 的真实版本与可执行检查；Python 要求恰为 3.12。

## 命令与路径

首次使用 `uv run --frozen --python 3.12 python`。运行中的 `{argv, cwd}` 已带绝对解释器和脚本路径。
终端支持 argv 时直接传数组；仅支持 PowerShell 文本时用 `&` 和逐参数单引号引用，参数内的单引号
写成两个单引号。不要用 `list2cmdline` 代替 PowerShell 引用，也不要添加 raw Coq 或构建参数。

脚本 checkout、目标 workspace 和调用者 cwd 可不同；生成的 invocation 固定正确位置。保留
C/formal stem 的区别和任意深度 collection/subdirectory 映射。物理 root 可含中文和空格，Rocq
logical path 各分量仍必须合法；原生工具自身对 source filename 的限制仍适用。

JSON 相对路径使用 `/`，Coq identity 不改大小写。先检查原始路径分量再规范化，拒绝 symlink、
junction、reparse point 和逃逸。不要用 subst 或链接绕过边界。UNC/cloud reparse workspace 不在
当前支持范围内。

## 文件、长度和恢复

Generated/staging 使用 UTF-8/LF，备份保留原 bytes。Group copies 独立写入，不继承 source 的只读
属性。正式替换在目标目录创建临时文件，flush/fsync 并关闭句柄后再 `os.replace`；不依赖跨盘移动。

Annotation 先独立生成，再发布有效输出。Final apply 保存短 role 文件名的 original/candidate
备份。恢复检查当前文件，发现外部修改或 sharing violation 时保留原件与备份，报告具体问题；
不无限重试，也不递归放宽 source tree 权限。

未启用系统 long paths 时，init 预检实际布局，包括 r10、生成临时目录、VC/group/parent build、
final replay/apply 和 backup。启用 LongPathsEnabled 不代表每个外部工具都支持长路径；优先缩短
物理 checkout，实测 Python、symexec、Coq 和 native backend，不自动添加 `\\?\` 前缀。

## 构建与进程

`_build` directory 选择 Dune，否则 Make。两者使用统一四字段 dependency plan 和 current 编译流程。
Dune 共享依赖刷新使用 workspace lock；Make 使用 exact 临时 Makefile，recipe 的 load paths 相对
绑定 cwd，避免重复长 root。Current 模块每次实际编译。

Coq check/debug 的 native 进程和 Dune 锁等待共享 900 秒预算。使用 `CREATE_NEW_PROCESS_GROUP`
及 `taskkill /T /F` 清理后代；零预算或已取消时不启动进程。成功清理后取回最终输出；Windows
运行中不保证部分 stdout/stderr。脱离后代仍持有管道时报告 `cleanup_incomplete`，避免同步关闭
被后台读取线程占用的流而无限阻塞。

Pause 只改变 control/signal，任务与 owner 保持原样；用户明确 resume 后重新派生动作。
日志与 timing 仅作诊断，不改变接纳结果。

## 验收范围

```powershell
uv run --frozen --python 3.12 python -m pytest .agents/scripts/tests -q
```

**本次重构尚未完成原生 Windows 验收。** Linux 测试或 mock 不能替代原生结果。Sharing violation
和 junction fixture 仅在 Windows 执行；工具存在时还需运行真实 Coq/Dune/Make smoke。
原生检查应覆盖中文/空格/括号/`&` root、分离 cwd、只读 source、r10 长路径、可选文件缺失、
取消、returned 接纳续跑及 publication 恢复，并保留实际结果。
