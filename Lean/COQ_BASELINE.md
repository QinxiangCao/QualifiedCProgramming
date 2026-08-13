# Coq Source Baseline

This repository is a Lean migration of the Coq repository at the exact
revision recorded below. The commit hashes, rather than branch names, are the
authoritative synchronization points.

## Parent Repository

| Field | Value |
| --- | --- |
| Baseline ID | `COQ-BASELINE-2026-07-21` |
| Recorded date | `2026-07-21` |
| Repository | `git@bitbucket.org:WxWyashen/annotated_simplec.git` |
| Branch at capture | `master` |
| Commit | `8e8fc0bd57a71cc92dc7ac93d8e675ab798b4ddb` |
| Commit subject | `update some examples` |

## Submodule Revisions

| Coq path | Commit | Source repository | Lean migration coverage |
| --- | --- | --- | --- |
| `GraphLib` | `dc30dfc2f7e935cef9e15dfbdd5361c09fc4811b` | `https://github.com/liukanooo/GraphLib.git` | No migrated slice yet |
| `MaxMinLib` | `ef0acd06e4adb617839b8faee7b37a407b97d38c` | `https://github.com/liukanooo/MaxMinLib.git` | No migrated slice yet |
| `MonadLib` | `71a41c57f060fcd56844d686c8003701843d9dd5` | `https://bitbucket.org/Wushushu/monadlib.git` | `MonadLib` |
| `compcert_lib` | `fec8f3f1000158e276e6b70b0a5931a761171e07` | `https://bitbucket.org/WxWyashen/compcert_lib.git` | `compcert_lib` |
| `fixedpoints` | `b04f77d684cd6337b5eb1889ca7709314f81c193` | `https://bitbucket.org/qinxiang-SJTU/fixedpoints.git` | `fixedpoints` |
| `listlib` | `78e816b1f679524f8d521e0fbfb2e4cb98a8d2d3` | `https://bitbucket.org/qinxiang-SJTU/listlib.git` | `auxlibs/AUXLib/ListLib` |
| `sets` | `276325c294a9f53d3513c039d6ef9c31b40c9d17` | `https://bitbucket.org/qinxiang-SJTU/sets.git` | `sets` |
| `sumlib` | `284f49973eb348148b26e8c27c92087460a0975b` | `https://bitbucket.org/qinxiang-SJTU/sumlib.git` | No migrated slice yet |
| `unifysl` | `f5160c97eef28c07266bfdee8e1a2fbaa5c20e59` | `https://bitbucket.org/qinxiang-SJTU/unifysl-prp.git` | `unifysl` |

Code originating directly in the parent `annotated_simplec` repository is
currently represented by `auxlibs`, `SeparationLogic`,
`examples`, and related integration files.

## Reproducing the Coq Checkout

```sh
git clone git@bitbucket.org:WxWyashen/annotated_simplec.git
cd annotated_simplec
git checkout 8e8fc0bd57a71cc92dc7ac93d8e675ab798b4ddb
git submodule update --init --recursive
git submodule status --recursive
```

At baseline capture time, the local `unifysl` checkout was reported as dirty
only because of an untracked `.DS_Store`; no Coq source file differed from the
pinned submodule commit.

For the declaration-level migration record, update procedure, and known
compatibility differences, see:

- [`docs/coq_source_baseline.md`](docs/coq_source_baseline.md)
- [`docs/migration_inconsistencies.md`](docs/migration_inconsistencies.md)
