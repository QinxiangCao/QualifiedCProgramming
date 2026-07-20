# Reference Cases 参考范围

reference case 只用于借鉴 proof style、tactic sequence 和 helper lemma shape。

## 范围

优先参考：

- `SeparationLogic/examples/LLM_bench`
- `QCP_demos_LLM`

允许但不推荐参考 `QCP_demos_human`。只读查看 human case 属于 allowed，不因读取本身产生 blocker。当前 group 是否可接受仍只取决于 assigned witness、helper/import 边界、当前 `source_goal_version` 绑定的 fixed group-check，以及后续 parent verify 和 final-check；若 formal files 引入 phase contract 不允许的库、import、generated artifact 或其他 formal dependency，才按合同拒绝。

## 可参考内容

- 同类 array split / merge proof。
- 同类 `replace_Znth` / `sublist` / `Zlength` helper。
- 同类 `safeExec` normalization。
- 同类 string memory proof。
- 同类 data-structure predicate unfold / fold proof。

## 不可复制

- 不属于当前 Markdown handoff / compact JSON result contract 的文件交接命名。
- helper lemmas 放在 `*_proof_manual.v` 的做法。
- `Admitted.`。
- 新 `Axiom`。
- generated file 的手工 patch。

若参考 proof 中 helper 放置位置不符合当前合同，改为 `group_worker_lib` helper，并由 parent verify 合并。
