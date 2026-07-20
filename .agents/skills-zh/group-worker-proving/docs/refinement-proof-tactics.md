# Refinement Proof 规则

本文件记录 refinement VC 中 `safeExec` 目标的稳定 proof pattern。

## Skeleton 模板

```coq
LLM_pre_process ltac:(lia || int_auto). (* or aggressive_pre_process for the strategy-processed branch *)
(* 1. 选择后条件 witnesses *)
Exists ... .
(* 2. 必要的空间化简 *)
simpl ... .
(* 3. 先拆空间目标和 execution 目标 *)
split_pure_spatial.
- (* spatial side *)
  ...
- (* safeExec side *)
  unfold wrapper_name in H at 1.
  prog_nf in H.
  unfold_loop in H.
  prog_nf in H.
  safe_choice_l H.  (* 或 safe_choice_r H *)
  ...
  exact H.
```

## 强制规则

1. LLM proof 先用 `LLM_pre_process ltac:(...)`，不要直接用 `pre_process.`；如果当前 VC 被打印成 `原始 VC \/ 策略应用后的 VC`，`LLM_pre_process` 选择原始分支，`aggressive_pre_process` 选择 strategy-processed 分支。solver 由 VC 分析决定：一般用 `ltac:(lia || int_auto)`，只在线性算术时用 `ltac:(lia)`，只在整数/位自动化时用 `ltac:(int_auto)`，确有非线性算术时才加入 `nia`。
2. 先选择 witnesses，再 `split_pure_spatial`。
3. 不在 `split_pure_spatial` 前展开 `safeExec` 相关 wrapper。
4. 先解决 spatial side，再解决 execution side。
5. execution side 中，每次 `unfold ... in H at 1` 或 `unfold_loop in H` 后，都执行 `prog_nf in H`。
6. normalized hypothesis 与 goal 匹配时，用 `exact H`。
7. 若 hypothesis 中是 `choice`，用 `safe_choice_l H` 或 `safe_choice_r H` 选择匹配分支。

## 允许 unfold

当 goal 是 `safeExec ?P prog X`：

- goal 中的 `prog` 是直接 wrapper application 时，可在 goal 中 unfold。
- 若 `prog` 已是 bind、choice、loop 等 compound expression，优先在 hypothesis 中 unfold。
- wrapper 名称只是 definitional equal 但不匹配时，可用 `change` 对齐名称，再 `exact H`。

非 `safeExec` 目标可正常使用 `unfold`、`simpl`、`lia`、`congruence` 等 tactic。

## `safeExec` 操作细节

进入 isolated `safeExec` goal 后，先找到当前 context 中承载 execution fact 的 hypothesis，通常形如：

```coq
H : safeExec ATrue (some_wrapper args) X
```

只在这个 hypothesis 上归一化：

```coq
unfold some_wrapper in H at 1.
prog_nf in H.
```

若出现 loop combinator：

```coq
unfold_loop in H.
prog_nf in H.
unfold loop_body in H at 1.
prog_nf in H.
```

若归一化后 hypothesis 与 goal 匹配：

```coq
exact H.
```

若 hypothesis 中出现 `choice`，用当前 branch fact 选择方向：

```coq
safe_choice_l H.  (* or safe_choice_r H *)
- exact H.
- lia.            (* assume!! side condition, ordinary Rocq proposition *)
```

`safe_choice_l/r` 产生的 guard goal 不是 `safeExec` goal；可用 `unfold`、`simpl`、`lia`、`congruence`、case-specific helper 等普通 tactics。

## Goal-side unfold

只有当 goal 的 program 是直接 wrapper application 时，才在 goal 中 unfold：

```coq
change (safeExec P (wrapper2 args) X).
unfold wrapper2.
prog_nf.
```

如果 goal 已经是 `bind`、`choice`、`repeat_break` 或其他 compound program，优先处理 hypothesis。不要在 goal 和 hypothesis 上同时 `unfold ... in *`，这会破坏可匹配的程序形态。

名称不一致但 definitionally equal 时，先 `change` 对齐：

```coq
change (safeExec P (old_name args ;; rest) X).
exact H.
```

## 禁止模式

不要使用以下低层 reconstruction：

- `safeExec_bind_reta`
- `safeExec_bind`
- 手工构造新的 `assert (Hs : safeExec ...)`
- `unfold ... in *` 处理 `safeExec` 相关定义
- 在 `prog_nf` 可解决处手动重关联 bind

这些模式容易和 generated VC 的程序形态错位。

更具体地说，不要为了证明 execution side 新造：

```coq
assert (Hs : safeExec P prog X).
```

也不要用低层 lemmas 手动重建 bind / ret / choice。generated VC 通常已经给出正确 execution hypothesis；正确做法是 unfold 当前 wrapper、`prog_nf in H`、选择 branch、`exact H`。

## 失败判断

若 `prog_nf in H`、`unfold_loop in H` 和正确的 `safe_choice_l/r` 后 abstract program state 仍无法和 goal 对齐，优先怀疑 annotation/spec 中的 abstract state 维护错误，而不是继续堆 tactic。

检查顺序：

1. witness 是否选错，导致后条件里的 abstract state tuple 不对。
2. spatial side 是否尚未把 resources 改成目标需要的 shape。
3. branch fact 是否指向另一条 `choice`。
4. loop-state tuple 是否和 annotation invariant 中的 `safeExec` residual 一致。
5. 当前 VC premise 是否缺少 annotation 应提供的 pure facts。

如果只是 wrapper 名称、list expression 或 arithmetic guard 不匹配，优先在 `group_worker_lib` 新增当前 suffix helper 或调整 proof；不要把 proof route 不确定写成 `blocked`。
