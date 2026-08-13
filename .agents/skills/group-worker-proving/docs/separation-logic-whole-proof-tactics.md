# Separation Logic Proof 规则

本文件记录 generated manual VC 中常见 `P |-- Q` 的 proof pattern。

## 基本流程

每个top-level VC只能使用handoff中controller-verified的route。`LLM_pre_process ltac:(...)`用于whole-goal route；`aggressive_pre_process.`用于strategy已经拆出且由本组先证明的split-goal route。两者都会展开VC、引入变量并提取部分pure facts。

## 强制骨架

只有两种合法的 proof 开头，按 declaration 种类固定：

有可用 split goals 的 top-level VC（`aggressive_pre_process` route）：

```coq
Proof.
  aggressive_pre_process.
  - Goal_apply <vc>_split_goal_1.
  - Goal_apply <vc>_split_goal_2.
Qed.
```

split goal，以及必须整体证明的 top-level VC（`LLM_pre_process` route）：

```coq
Proof.
  LLM_pre_process ltac:(<closer>).
  ...
Qed.
```

硬性要求：

- `aggressive_pre_process.` 之后只允许 `Goal_apply <对应split-goal lemma>.`，每个分支一条，不写其他 tactic。top-level proof 只是分派层。
- 每个 split goal 的第一个 tactic 必须是 `LLM_pre_process ltac:(...)`，并显式写出 closer（通常 `ltac:(lia || nia || int_auto)`）。
- 不得使用别名 `pre_process`。它等价于 `LLM_pre_process ltac:(lia || nia || int_auto)`（`CommonAssertion.v`），但隐藏了 closer，禁止在 proof 文本中出现。
- 不得用手写 `unfold <goal_name>.` + `intros ...` 代替 `LLM_pre_process`。

当前 symexec printer 可能把最终 VC 打印为：

```coq
original_vc \/ vc_after_strategies
```

`LLM_pre_process` 已在内部选择 original branch，`aggressive_pre_process` 已在内部选择 strategy-processed branch；不要在这些 tactic 前手写 `left;` 或 `right;`。

生成的`<vc_name>_split_goal_*` declarations不是可删除的辅助信息：

- handoff选择`aggressive_pre_process`时，它们是assigned正式子目标。逐个只修改proof span、按上面的强制骨架以`LLM_pre_process ltac:(...)`开头、完成proof并`Qed.`；然后在top-level VC中执行`aggressive_pre_process`，对产生的各分支只执行`Goal_apply <对应split-goal lemma>.`。不得用`apply`、`eapply`、`exact`、`refine`或局部别名替代`Goal_apply`。除禁用 tactic 由 controller 扫描外，骨架其余部分是worker原则，不由controller检查tactic文本。
- handoff选择`LLM_pre_process`时，只证明top-level whole goal。这些generated split-goal不进入本route，其Rocq token必须仍是`Proof. Abort.`；不要“顺手完成”它们。注释、空白、CRLF/LF和EOF换行不影响该检查。

不要自行改变route；若controller-verified route在current proof state中出现语义缺口，记录具体state并blocked/回annotation。

## 证明复用提示

若group handoff给出`proof_reuse.md`，严格按全部helper rows → 全部aggressive split-goal rows → 全部`LLM_pre_process` top-level rows读取引用的previous current-run file和exact line range；aggressive top-level VC没有复用行。非from-scratch range覆盖parser识别的整个declaration，而不是其中若干tactic行。sealed source可能是failed proving round，也可能是verified后因annotation/freshness retry而stale的round；结构非法failed group已被跳过。helper/proof `direct copy`只来自previous controller-validated accepted group；manual proof direct还要求generated-goal语义指纹一致，允许仅generated declaration改名。未accepted source proof最多提供`partial proof-idea reuse`，其helper须from scratch。worker仍须按current binders、hypotheses与proof mode重新检查；指纹变化时按hint重建adapter/frame，或from scratch。hint不允许修改previous files，也不替代当前debug、development/exact check；handoff为none时不要扫描旧round。

split goal由`P |-- Q`变化为`P' |-- Q'`时，先尝试把旧proof包在两个adapter之间：证明`P |-- P'`进入旧前提，再证明`Q' |-- Q`回到新结论。若只增加、消去或重排共同spatial frame，则明确使用cancel/frame转换并检查side conditions。这些属于`partial proof-idea reuse`，不是逐字direct copy。Reason只是设计提示，实际adapter必须由本组proof检查。单witness group应利用hint中的helper/split components；multi-witness group不要假设一个group helper机械服务每个witness。

aggressive route的典型结构是先完成split declarations，再完成top-level declaration：

```coq
Lemma proof_of_x_split_goal_1 : (* generated statement *).
Proof.
  (* prove this exact split goal *)
Qed.

Lemma proof_of_x : (* generated statement *).
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_x_split_goal_1.
Qed.
```

实际subgoal数量和`Goal_apply`顺序以current proof state与handoff为准，不要从示例猜参数。split-goal proof body内部仍可正常使用其他tactic和数学helper；限制只针对aggressive top-level VC应用assigned split lemmas的方式。

## `Intros` / `Intros_p` 策略

- `Intros x.`：引入前条件中的 `EX x`。
- `Intros x y.`：连续引入多个 existential witnesses。
- `Intros_p H.`：引入前条件中的 pure fact `[| P |]`。

若 proof state 中还有未命名 existential 或 pure facts，先显式引入，再做 `cancel` / `sep_apply` / arithmetic。

## `Exists` 策略

`Exists x.` 或 `Exists x y.` 用来实例化后条件中的 existential witnesses。先根据交接中该 witness 的 `Strategy:` 行（`aggressive_pre_process` route 则用对应 split goal 的 strategy）选择值，例如旧逻辑列表、`replace_Znth(i, v, l)`、`sublist(lo, hi, l)`、`l ++ [v]` 或当前 abstract state。

不要等空间目标复杂化后再猜 existential。

## `cancel` 策略

`cancel P.` 消去前后条件中形式完全相同的空间资源。若资源只是在算术上等价，先用 pure facts rewrite 或 normalize。当前后只剩 `P |-- P` 时，`cancel P` 通常可完成目标。

## `sep_apply_l_atomic` / `sep_apply_r_atomic` 策略

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

## `prop_apply_p` 策略

`prop_apply_p (Lemma args premises).` 用 separation-logic lemma 从前条件资源推出新的 pure fact，并把 `[| R |]` 加回前条件。

适用场景：

- 从 list / struct predicate 推出 non-null、length、shape 或 segment relation。
- 在 `sep_apply_*` 前先导出一个 side condition。
- 将当前 spatial resource 暴露成后续 arithmetic / list proof 可用的 pure hypothesis。

要求显式实例化所有参数和 lemma premise。若 premise 无法由当前 context 证明，不要伪造；回到 annotation 或新增当前 group suffix helper。handoff frozen snapshot中声明/proof token一致的sealed helper可以复制并保留其历史suffix，实质修改后的版本必须换为当前suffix。

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
LLM_pre_process ltac:(lia || nia || int_auto).
Intros ...
Intros_p ...
Exists ...
split_pure_spatial.
- cancel ...
- split_pures.
  + dump_pre_spatial. lia.
```

`entailer!` 是禁用 tactic，不得出现在 proof 文本中；`LLM_pre_process` 与 `Goal_apply` 内部的调用不受影响。

`lia` 不是 proof plan。先确认 context 中已有 index bounds、list length facts、loop guard、branch condition、`@pre` bridge 和 array read binding。缺失这些 facts 时，应回到 annotation 或 vc-checking。

纯目标常见处理顺序：

```coq
split_pures.
- dump_pre_spatial. subst. lia.
- dump_pre_spatial. rewrite Zlength_app. rewrite Zlength_cons. lia.
- dump_pre_spatial. eapply some_case_helper__gid; eauto.
```

对 list equality，先尝试已有 `sublist` / `replace_Znth` / `Zlength` lemma；缺少稳定连接事实时，把新helper放入 `group_worker_lib`并使用当前group suffix。与public/reuse sealed helper声明/proof token一致时允许保留来源suffix。

## Array / string goals 处理

array proof 常见步骤：从 `full` / `seg` 得到 `Zlength`，split 当前 index，写回后 merge 到 `full` / `seg`，用 `replace_Znth`、`sublist`、`Znth` pure lemma 证明列表关系。

string proof 常见步骤：展开 `store_string` / `c_string` / `string_length`，处理结尾 `0`，区分 Rocq `string` 和 `list Z`。

需要 helper lemma 时，新增到 `group_worker_lib` 并证明；不要写入 `*_proof_manual.v`。turn开始只浏览handoff的round-start frozen public snapshot，把可能有用且声明/proof token一致的proved declarations及必要官方imports复制到local lib；不直接import或编辑snapshot/durable pool，复制后即使最终unused也合法，但仍须通过本组check。

## 整体证明骨架

常见 entailment proof：

```coq
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
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

## 失败信号

优先改 proof / helper：

- goal 是 list arithmetic、`sublist`、`replace_Znth`、`Permutation` 或 bound bridge。
- spatial resource 需要一个已知 split / merge lemma。
- annotation 已经暴露所有必要 bounds 和 branch facts。

优先退回 annotation：

- premise 中没有当前 index bounds、branch condition、array read binding 或 `@pre` bridge。
- postcondition 需要的 heap resource 在前条件中已经丢失。
- witness statement 要求的 functional fact 完全不在 invariant / `Ensure` 中出现。
