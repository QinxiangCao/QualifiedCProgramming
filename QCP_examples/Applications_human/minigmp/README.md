# 独立 MiniGMP（非 SumLib）

本目录及对应的 `Rocq/examples/Applications_human/minigmp/` 恢复自迁移前提交
`9e3d56646c8ba3644d689f2ef829c6c5d33e3bf8`。原 `gmp.c`、策略及保留的原证明
保持原样；重复的历史 split 副本已删除，见下文。原规格修复仅涉及 `mini-gmp.h` 中误写为交换的 `mpz_neg`：
修正为取负，新增独立 `mpz_neg.c` 及证明，不改动原 `gmp.c` 证明。

统一 SumLib 版本仍在 `../gmp/minigmp/`，FME/GE 使用该版本。两套源码及 Rocq
命名空间独立，不能放在同一个 spec-check 项目作用域中互相覆盖声明。

从仓库根检查原版的规格与全部有效证明模块：

```powershell
& ./bin/windows/spec-check.exe QCP_examples/Applications_human/minigmp -I QCP_examples/Applications_human --given-contracts QCP_examples/Applications_human/minigmp/given-contracts.tsv
if ($LASTEXITCODE -ne 0) { throw "MiniGMP specification check failed" }
.\dune.cmd build -j1 '@Rocq/examples/Applications_human/minigmp/all'
```

SumLib 版本及 FME/GE 的检查命令见 [SumLib GMP README](../gmp/README.md#验收)。

局部 Makefile 提供 `all`、`check`、`generate`；总 Rocq Makefile 和平台 example
runner 同时列入两套版本。生成会覆盖 generated manual，常规验收只编译现有证明。
`check` 依次运行 SpecCheck 和证明编译；这两项不检查证明中的占位声明，不能代替证明闭合性审查。

原有六个 `gmp_proof_manual_part<N>.v` 历史副本已删除。其中全部 190 个 lemma
的 statement 已逐项确认与完整 `gmp_proof_manual.v` 中对应 lemma 一致；
实际 goal-check 使用完整主文件。验收编译本目录全部 Rocq 模块，无副本排除规则。

`given-contracts.tsv` 只接受原头文件 Given Functions 段内六个原语的精确契约。
其中分配、释放契约在新的独立翻译单元中各出现一次，因此共八条作用域匹配项，
仍只有原来的六个原语及六种契约，标为 ASSUMED，不计入 VERIFIED；
不包含 `mpz_neg` 或其他待证明函数。
