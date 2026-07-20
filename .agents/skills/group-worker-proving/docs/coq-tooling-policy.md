# Coq Tooling

`controller.py coq-check/coq-debug` 是唯一外部 Coq 入口。group-worker原样执行 `group_worker_input.md` 中的两个命令，不直接调用 `coq_tooling.py`、raw `coqc`/`coqtop`、Dune、Rocq MCP或`_CoqProject` command。

## Directory/overlay

- 完整 formal dependencies来自 main root。
- group directory只有 copied manual与`group_worker_lib`。
- controller从 current state/manifest派生两个 overlay destinations。
- build固定在 current run `_coq_builds/<round>/<group>/src`。
- debug script只写 handoff给出的 exact `.coq_debug` path。

failed proof feedback只授权修改 assigned bodies、`group_worker_lib`或 declared debug script；不授权修改 command、path、flag、unassigned witness、statement或`formal_case_lib`。

## Completion

exact group-check必须 passed且版本 current，才能写 `group_worker_report.json.status = completed`。report不粘贴 Coq argv、cwd、source digest清单或完整 evidence；controller review会重跑同一 fixed group-check，并把compact status写入 controller state。parent verify还会再次检查 group内容并运行 full goal check。

Coq tooling使用`SeparationLogic/CONFIGURE`和Makefile配置的可执行文件。基础`.vo`复用不是current run私有cache，而是所有run和所有Coq阶段共同使用main root前置全量make产物的系统级规则；Makefile全部`-R`/`-Q` load path都会按check stage到run build，不为基础库建立源码digest/Coq版本/flags cache，也不在group或parent check重编译基础源码。current target case的lib/goal/auto/manual/check五个module不受此信任：旧产物会被排除，group overlay及current generated source会重新编译。required基础`.vo`缺失时应让exact check失败并报告，不得改用raw Coq补编基础库。
