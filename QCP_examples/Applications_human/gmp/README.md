# SumLib MiniGMP 与应用

本目录是联合检查的项目边界。`minigmp/` 提供共享 GMP 实现和规格，`fme/` 与
`ge/` 分别提供 Fourier–Motzkin 消元与高斯消元应用。对应证明位于
`Rocq/examples/Applications_human/gmp/`，逻辑命名空间为
`SimpleC.EE.Applications_human.gmp`。库以 SumLib 数值模型为基础。

原 `minigmp_sumlib` 和 `fme_ge_gmp` 已合并到本目录。
不基于 SumLib 的独立版本保留在 `../minigmp/`，证明位于对应的 Rocq 目录，
使用独立命名空间；FME/GE 继续只使用本目录中的 SumLib 版本。
统一版本包含 70 个 C 案例和 7 套策略，保留基础版 24 个已实现函数的能力。
每个共享函数只保留一个实现；原地更新、非别名、raw/preserving、plain/read0
规格按各自内存前提保留。函数规格推导必须同时检查生成的 derive VC。

## 生成与构建入口

局部 Makefile 位于 `Rocq/examples/Applications_human/gmp/Makefile`。在该目录中，
`qcp-case-gmp-<case>`、`qcp-case-fme-<case>`、`qcp-case-ge-<case>` 生成单个案例；
`case-gmp-<case>`、`case-fme-<case>`、`case-ge-<case>` 编译对应案例及依赖。
`generate-gmp`、`generate-fme`、`generate-ge` 提供分层生成入口，
`gmp-artifacts`、`fme-artifacts`、`ge-artifacts` 提供分层编译入口。
生成会刷新 `<case>_goal.v`、`<case>_proof_auto.v`、`<case>_proof_manual.v` 和
`<case>_goal_check.v`，使用前应保留已有手工证明。代理执行单案例验证时仍遵循
仓库 `AGENTS.md` 中的 verification-orchestrator 流程。

三个子目录各自拥有 Dune theory；FME/GE 依赖公共 MiniGMP theory。父目录仅组织
子目录，不再额外声明空的 umbrella theory。

## 验收

从仓库根依次运行 SpecCheck 和证明编译（检查器需包含 Given Functions 支持）：

```powershell
& ./bin/windows/spec-check.exe QCP_examples/Applications_human/gmp -I QCP_examples/Applications_human --given-contracts QCP_examples/Applications_human/gmp/given-contracts.tsv
if ($LASTEXITCODE -ne 0) { throw "GMP specification check failed" }
.\dune.cmd build -j1 '@Rocq/examples/Applications_human/gmp/all'
```

SpecCheck 联合扫描本目录的库与应用；Dune 编译三个子目录的全部证明模块，
包括 `*_goal_check.v` 和 `*_lib.v`。Windows 使用仓库 `dune.cmd`，
Linux/macOS 使用 `dune`，SpecCheck 分别使用 `bin/linux/spec-check` 或
`bin/macos-{arm64,x86_64}/spec-check`；`-j1` 可按需要调整。仅检查声明覆盖时只运行第一条命令，
需要 JSON 报告时为 SpecCheck 添加 `--json <文件路径>`。

`given-contracts.tsv` 列出 14 个外部分配、释放和交换原语的 16 项精确契约及其理由。它将匹配到的
规格标为 `ASSUMED`，不计入 `VERIFIED`。签名、规格或项目作用域变化需要重新审查
清单。不能将缺少算法证明的规格加入这份清单。

GE 数组模型另沿用 `GeGmpArray.sizeof_mpz_struct` 这一 ABI 假设：在本项目的
32 位内存模型中，`__mpz_struct` 占 12 字节。它是 Rocq 模型前提，不属于 C
声明覆盖清单中的 Given Functions。

`spec-check` 本身只检查声明覆盖，JSON 的 `proofsChecked` 为 `false`。
上述命令不扫描 `Admitted`、`admit` 或假设声明。Dune 编译成功也不能代替证明闭合性审查；
完整入口会加载 auto 模块，但不会审计其中内容。手工证明、规格推导、`goal_check`
接线及各模块的假设仍需单独审查。
