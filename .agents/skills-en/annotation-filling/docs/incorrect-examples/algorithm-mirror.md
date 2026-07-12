# Incorrect Example: Algorithm Mirror Spec

本文件是 annotation 反例解析。它说明为什么不要先在 `case_lib` 中写一份 Rocq 版 C 算法，再让 annotation 追踪这份算法。

## Example Files

本目录中的相关文件：

- `algorithm-mirror.md`：反例解析，概括 algorithm-mirror spec 为什么应回退。
- `max_sub_array.c`：完整反例 C annotation。
- `max_sub_array_lib.v`：反例 `case_lib`，包含追踪 Kadane-style loop 的 Rocq mirror definitions。
- `max_sub_array_goal.v`：generated VC artifact，用于观察这种 spec 如何把 VC 结构拖向算法同步证明；proof / check artifacts 不作为反例素材保留。

这些文件不是模板。读取它们是为了识别坏 spec 和坏 invariant 的形状，并在当前 case 中及时回到 predicate-first 设计。

## Bad Pattern

常见坏路线：

```coq
Fixpoint c_loop_mirror (state : LoopState) (fuel : nat) : LoopState := ...
Definition answer_spec input out :=
  out = extract_answer (c_loop_mirror (init_state input) fuel).
```

然后 C annotation 写成：

```c
Inv Assert
  exists st,
    st == c_loop_mirror(init_state(l), i) &&
    local_x == extract_x(st) &&
    IntArray::full(a, n, l)
```

这通常是错方向，即使 Rocq 定义本身能通过 `coqc`。

## Why It Fails

- spec 只说明“另一份程序怎么跑”，不是说明目标数学性质。
- loop invariant 隐藏了真正需要的 prefix / suffix / bounds / candidate answer。
- generated VC 会变成“C loop 与 Rocq mirror 同步前进”，证明脆弱且难返工。
- 一旦 C 局部控制流或 annotation 需要调整，Rocq mirror 和 proofs 会连锁失效。

`max_sub_array` 反例属于这种形态：在 Rocq 中定义类似 Kadane loop 的递归器，再让 annotation 追踪该递归器。更好的 spec 是定义最大子数组和的数学语义，并在 loop invariant 中直接维护当前前缀的最大 suffix、当前前缀的最大 subarray、bounds 和数组资源。

## Replace With Predicate-First Annotation

先问当前程序点真正维护什么数学事实：

- 已处理前缀和未处理后缀分别是什么？
- 当前候选值表示哪类最优性、边界或约束？
- 数组资源是整体 `full`、区间 `seg`，还是 shape / undef 组合？
- 函数出口需要证明输入输出之间的哪个数学关系？

改成：

```coq
Definition MaxSubarraySumPrefix (l : list Z) (i best suffix_best : Z) : Prop := ...
Definition MaxSubarraySum (l : list Z) (ans : Z) : Prop := ...
```

```c
Inv Assert
  0 <= i && i <= n@pre &&
  MaxSubarraySumPrefix(l, i, best, suffix_best) &&
  IntArray::full(a, n@pre, l)
```

如果 proof 需要连接 lemma，把 lemma 放到 group-local `case_lib` 由 group-worker 证明，或在 annotation round 中提升为 seed spec declaration；不要把 helper 写进 `*_proof_manual.v`。

## Immediate Rework Signals

看到以下信号时，先回到 annotation/spec，而不是进入 vc-proving：

- 新 `Fixpoint` 的参数几乎就是 C loop locals。
- invariant 的核心字段是 `state_after_k_steps`、`run_loop`、`simulate` 之类执行器。
- `Ensure` 只能被同一个算法 mirror 解释，无法用于另一个实现。
- proof failure 反复要求证明 C 单步和 Rocq 单步同步。

## What To Learn From `max_sub_array`

反例的核心问题不是 Rocq definition 本身不能写，而是 annotation 方向错误：

- `case_lib` 中的定义追踪 C loop 状态，而不是独立数学性质。
- C invariant 依赖 algorithm mirror 的中间状态，隐藏了 prefix / suffix / optimum / bounds 等真正应暴露的 facts。
- manual VC 容易变成证明 C step 与 Rocq step 同步，而不是证明 C 程序满足数学 spec。

遇到类似形态时，先回到 `annotation-guide.md` 的 predicate-first 设计：

- 定义最大子数组和、最大 suffix、处理前缀等数学 predicate。
- 在 loop invariant 中直接维护当前前缀的最优性和数组资源。
- 把纯 list / max-min bridge 留给 group-worker helper，不要让 C annotation 追踪一份 Rocq loop interpreter。
