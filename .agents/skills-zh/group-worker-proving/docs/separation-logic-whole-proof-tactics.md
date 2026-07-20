# Separation Logic Proof 规则

本文件记录 generated manual VC 中常见 `P |-- Q` 的 proof pattern。

## 基本流程

LLM 写 manual proof 时通常从 `LLM_pre_process ltac:(lia || int_auto).` 开始，用于展开 VC、引入变量并提取部分 pure facts。不要在 LLM proof 中直接使用 `pre_process.` 或 `entailer!.`。

当前 symexec printer 可能把最终 VC 打印为：

```coq
original_vc \/ vc_after_strategies
```

`LLM_pre_process` 用于 original branch，`aggressive_pre_process` 用于 strategy-processed branch；不要在这些 tactic 前手写 `left;` 或 `right;`。

`LLM_pre_process ltac:(...)` 中的 solver 由当前 VC 分析决定：

- 一般先用 `LLM_pre_process ltac:(lia || int_auto).`。
- 只需要线性算术时用 `LLM_pre_process ltac:(lia).`。
- 只需要整数/位自动化时用 `LLM_pre_process ltac:(int_auto).`。
- 只有确实有非线性算术（例如乘法关系、平方、乘积比较）且 `lia` 不适用时，才加入 `nia`，例如 `LLM_pre_process ltac:(lia || int_auto || nia).`。
- `pre_process` / `pre_process_default` 只是兼容别名；LLM 生成或修复 proof 时不要调用它们。

生成的 `<vc_name>_split_goal_*` lemma 若以 `Proof. Abort.` 结束，只是 diagnostics，不是最终 `VC_Correct` obligation。

## 生成 split-goal 证明路线

对于已经生成 `<vc_name>_split_goal_*` definitions 的 strategy-processed obligations，先证明每个 generated
split goal：

```coq
Lemma proof_of_<vc>_split_goal_1 : <vc>_split_goal_1.
Proof.
  pre_process.
  ...
Qed.
```

然后主 witness proof 只保留为 glue：

```coq
Lemma proof_of_<vc> : <vc>.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_<vc>_split_goal_1.
  - Goal_apply proof_of_<vc>_split_goal_2.
Qed.
```

`Goal_apply` 是有意保持轻量的 tactic：它只会按相同类型从上下文 hypothesis 中 greedy 实例化
`forall` 参数，然后应用 split-goal lemma，并要求当前 goal 被完全解决。

如果 `Goal_apply` 报错：

```text
Goal_apply: greedy instantiation did not completely solve the goal
```

通常原因是上下文中有多个同类型参数，例如多个 `Z` 变量或多个 `tree` 变量，greedy 实例化选错后留下了
residual separation-logic goal。不要增强 `Goal_apply` 的搜索；能成功的 split-goal branch 继续保留
`Goal_apply`，只把失败的 branch 改成显式参数：

```coq
sep_apply (proof_of_some_split_goal
  arg1 arg2 arg3 premise1 premise2);
entailer!.
```

对于 pure non-separation goal，若 goal shape definitionally match，使用
`exact (proof_of_some_split_goal args...).`。若只差 separation conjunction associativity 或 `TT && emp`
simplification，使用 `sep_apply`。

## `Intros` / `Intros_p`

- `Intros x.`：引入前条件中的 `EX x`。
- `Intros x y.`：连续引入多个 existential witnesses。
- `Intros_p H.`：引入前条件中的 pure fact `[| P |]`。

若 proof state 中还有未命名 existential 或 pure facts，先显式引入，再做 `cancel` / `sep_apply` / arithmetic。

## `Exists`

`Exists x.` 或 `Exists x y.` 用来实例化后条件中的 existential witnesses。先根据 vc-checking 的 `witness_instantiation` 选择值，例如旧逻辑列表、`replace_Znth(i, v, l)`、`sublist(lo, hi, l)`、`l ++ [v]` 或当前 abstract state。

不要等空间目标复杂化后再猜 existential。

## `cancel`

`cancel P.` 消去前后条件中形式完全相同的空间资源。若资源只是在算术上等价，先用 pure facts rewrite 或 normalize。当前后只剩 `P |-- P` 时，`cancel P` 通常可完成目标。

## `sep_apply_l_atomic` / `sep_apply_r_atomic`

- `sep_apply_l_atomic (Lemma args).`：把前条件中的资源变成 lemma 结论形态。
- `sep_apply_r_atomic (Lemma args).`：把后条件中的资源展开成 lemma 前提形态。

必须显式实例化 lemma 参数。若 lemma 有 pure premise，side goals 应由当前 annotation 暴露的 pure facts 解决。

典型 side goal 形态：

```coq
M |-- [| p <> NULL |]
```

先引入已有 pure facts，再用 `dump_pre_spatial.` 进入普通 Rocq proposition：

```coq
Intros_p Hneq.
dump_pre_spatial.
unfold NULL in *.
lia.
```

不要把需要的 pure premise 临时写成 `admit` 或改 witness statement。若 premise 不在当前 VC 中，优先检查 annotation 是否缺 branch fact、bounds、array read binding 或 `@pre` bridge。

## `prop_apply_p`

`prop_apply_p (Lemma args premises).` 用 separation-logic lemma 从前条件资源推出新的 pure fact，并把 `[| R |]` 加回前条件。

适用场景：

- 从 list / struct predicate 推出 non-null、length、shape 或 segment relation。
- 在 `sep_apply_*` 前先导出一个 side condition。
- 将当前 spatial resource 暴露成后续 arithmetic / list proof 可用的 pure hypothesis。

要求显式实例化所有参数和 lemma premise。若 premise 无法由当前 context 证明，不要伪造；回到 annotation 或新增当前 group suffix helper。

## Disjunction 和 Universal

- `Left.`：证明 `P |-- Q || R` 的左侧。
- `Right.`：证明 `P |-- Q || R` 的右侧。
- `Split.`：把 `P || Q |-- R` 拆成两个 goals。
- `Intros_r x.`：引入后条件中的 `ALL x`。

选择 `Left` / `Right` 前先看 branch fact、loop guard 或 constructor shape。不要为了让 proof 走通任意选分支；选错分支通常会留下无法证明的 pure goal。

## Pure goal 工具

`split_pures.` 把后条件中的多个 pure conjunct 拆成独立 goals。

`dump_pre_spatial.` 丢弃前条件中的 spatial 部分，把 `P |-- [| Q |]` 变成普通 Rocq goal `Q`，只在已经把需要的 pure facts 都引入后使用。

## Pure goals 处理

常见流程：

```coq
LLM_pre_process ltac:(lia || int_auto).
Intros ...
Intros_p ...
Exists ...
split_pures.
- dump_pre_spatial. lia.
```

`lia` 不是 proof plan。先确认 context 中已有 index bounds、list length facts、loop guard、branch condition、`@pre` bridge 和 array read binding。缺失这些 facts 时，应回到 annotation 或 vc-checking。

纯目标常见处理顺序：

```coq
split_pures.
- dump_pre_spatial. subst. lia.
- dump_pre_spatial. rewrite Zlength_app. rewrite Zlength_cons. lia.
- dump_pre_spatial. eapply some_case_helper__gid; eauto.
```

对 list equality，先尝试已有 `sublist` / `replace_Znth` / `Zlength` lemma；缺少稳定连接事实时，把 helper 放入 `group_worker_lib`，名称必须以当前 group suffix 结尾。

## Array / string goals 处理

array proof 常见步骤：从 `full` / `seg` 得到 `Zlength`，split 当前 index，写回后 merge 到 `full` / `seg`，用 `replace_Znth`、`sublist`、`Znth` pure lemma 证明列表关系。

string proof 常见步骤：展开 `store_string` / `c_string` / `string_length`，处理结尾 `0`，区分 Rocq `string` 和 `list Z`。

需要 helper lemma 时，新增到 `group_worker_lib` 并证明；不要写入 `*_proof_manual.v`。

## Whole-proof Skeleton

常见 entailment proof：

```coq
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Intros x y.
  Intros_p Hbounds.
  Exists witness1 witness2.
  split_pure_spatial.
  - cancel (SomePred p l).
    sep_apply_l_atomic (some_left_lemma arg1 arg2).
    + dump_pre_spatial. lia.
    + sep_apply_r_atomic (some_right_lemma arg3).
      cancel (TargetPred p l').
  - split_pures.
    + dump_pre_spatial. subst. lia.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
Qed.
```

如果 `cancel P` 不匹配，先检查两边是否形式上相同。`cancel` 不会帮你把语义相等但语法不同的 resources 化简；需要先 rewrite pure equalities、normalize list expressions，或用 `sep_apply_*_atomic` 改 resource shape。

## Failure Signals

优先改 proof / helper：

- goal 是 list arithmetic、`sublist`、`replace_Znth`、`Permutation` 或 bound bridge。
- spatial resource 需要一个已知 split / merge lemma。
- annotation 已经暴露所有必要 bounds 和 branch facts。

优先退回 annotation：

- premise 中没有当前 index bounds、branch condition、array read binding 或 `@pre` bridge。
- postcondition 需要的 heap resource 在前条件中已经丢失。
- witness statement 要求的 functional fact 完全不在 invariant / `Ensure` 中出现。
