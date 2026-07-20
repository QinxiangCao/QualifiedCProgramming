# Separation-Logic Proof Rules

This document records common proof patterns for generated manual VCs of the form `P |-- Q`.

## Basic workflow

When writing manual proofs, LLM agents should usually start with `LLM_pre_process ltac:(lia || int_auto).` to unfold the VC, introduce variables, and extract some pure facts. Do not call `pre_process.` or `entailer!.` directly in LLM-written proofs.

The current symbolic-execution printer may produce the final VC as:

```coq
original_vc \/ vc_after_strategies
```

Use `LLM_pre_process` for the original branch and `aggressive_pre_process` for the strategy-processed branch. Do not write `left;` or `right;` before those tactics.

Choose the solver inside `LLM_pre_process ltac:(...)` from the current VC:

- Usually start with `LLM_pre_process ltac:(lia || int_auto).`.
- If only linear arithmetic is needed, use `LLM_pre_process ltac:(lia).`.
- If only integer/bit automation is needed, use `LLM_pre_process ltac:(int_auto).`.
- Add `nia` only for genuinely nonlinear arithmetic, such as multiplication facts, squares, or product comparisons, and only when `lia` is not applicable; for example, `LLM_pre_process ltac:(lia || int_auto || nia).`.
- `pre_process` / `pre_process_default` are compatibility aliases only. Do not use them when generating or repairing LLM proof scripts.

A generated `<vc_name>_split_goal_*` lemma ending in `Proof. Abort.` is only a diagnostic and is not a final `VC_Correct` obligation.

## Generated Split-Goal Route

For strategy-processed obligations with generated `<vc_name>_split_goal_*` definitions, first prove the
generated split goals:

```coq
Lemma proof_of_<vc>_split_goal_1 : <vc>_split_goal_1.
Proof.
  pre_process.
  ...
Qed.
```

Then keep the main witness proof as glue:

```coq
Lemma proof_of_<vc> : <vc>.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_<vc>_split_goal_1.
  - Goal_apply proof_of_<vc>_split_goal_2.
Qed.
```

`Goal_apply` is intentionally lightweight: it greedily instantiates `forall` parameters from same-typed
hypotheses, applies the split-goal lemma, and requires the current goal to be completely solved.

If `Goal_apply` fails with:

```text
Goal_apply: greedy instantiation did not completely solve the goal
```

the usual cause is ambiguous same-typed parameters, such as several `Z` or `tree` variables in the context.
Do not make `Goal_apply` search harder. Keep successful split-goal branches as `Goal_apply`, and replace
only the failing branch with explicit parameters:

```coq
sep_apply (proof_of_some_split_goal
  arg1 arg2 arg3 premise1 premise2);
entailer!.
```

For pure non-separation goals, use `exact (proof_of_some_split_goal args...).` when the goal shape matches
definitionally. Use `sep_apply` when the goal differs only by separation-conjunction associativity or by
`TT && emp` simplification.

## `Intros` / `Intros_p`

- `Intros x.` introduces an `EX x` from the precondition.
- `Intros x y.` introduces several existential witnesses in sequence.
- `Intros_p H.` introduces a pure fact `[| P |]` from the precondition.

If unnamed existentials or pure facts remain in the proof state, introduce them explicitly before using `cancel`, `sep_apply`, or arithmetic.

## `Exists`

Use `Exists x.` or `Exists x y.` to instantiate postcondition existentials. Choose values according to vc-checking's `witness_instantiation`, such as the old logical list, `replace_Znth(i, v, l)`, `sublist(lo, hi, l)`, `l ++ [v]`, or the current abstract state.

Do not postpone existential choices until the spatial goal is already complicated.

## `cancel`

`cancel P.` removes spatial resources that are syntactically identical in the pre- and postconditions. If resources are only arithmetically equivalent, first rewrite or normalize them using pure facts. When the goal is reduced to `P |-- P`, `cancel P` usually closes it.

## `sep_apply_l_atomic` / `sep_apply_r_atomic`

- `sep_apply_l_atomic (Lemma args).` transforms a precondition resource into the lemma's conclusion shape.
- `sep_apply_r_atomic (Lemma args).` expands a postcondition resource into the lemma's premise shape.

Instantiate lemma parameters explicitly. If a lemma has pure premises, current annotation-exposed pure facts must solve the side goals.

A typical side goal is:

```coq
M |-- [| p <> NULL |]
```

First introduce available pure facts, then use `dump_pre_spatial.` to enter an ordinary Rocq proposition:

```coq
Intros_p Hneq.
dump_pre_spatial.
unfold NULL in *.
lia.
```

Do not temporarily `admit` a necessary pure premise or change the witness statement. If the premise is absent from the current VC, first check for a missing annotation branch fact, bound, array-read binding, or `@pre` bridge.

## `prop_apply_p`

`prop_apply_p (Lemma args premises).` uses a separation-logic lemma to derive a new pure fact from precondition resources and adds `[| R |]` back to the precondition.

Use it to:

- Derive a non-null, length, shape, or segment relationship from a list/structure predicate.
- Export a side condition before `sep_apply_*`.
- Turn the current spatial resource into a pure hypothesis usable by arithmetic or list reasoning.

Instantiate every parameter and premise explicitly. If a premise cannot be proved from the current context, do not fabricate it; return to the annotation or add a current-group-suffixed helper.

## Disjunction and universal quantification

- `Left.` proves the left side of `P |-- Q || R`.
- `Right.` proves the right side of `P |-- Q || R`.
- `Split.` turns `P || Q |-- R` into two goals.
- `Intros_r x.` introduces an `ALL x` from the postcondition.

Before choosing `Left` or `Right`, inspect the branch fact, loop guard, or constructor shape. Do not select an arbitrary branch merely to advance the script; the wrong branch usually leaves an impossible pure goal.

## Pure-goal tools

`split_pures.` splits several pure postcondition conjuncts into separate goals.

`dump_pre_spatial.` discards the spatial part of the precondition and changes `P |-- [| Q |]` into an ordinary Rocq goal `Q`. Use it only after introducing all required pure facts.

## Handling pure goals

A common flow is:

```coq
LLM_pre_process ltac:(lia || int_auto).
Intros ...
Intros_p ...
Exists ...
split_pures.
- dump_pre_spatial. lia.
```

`lia` is not a proof plan. First ensure that the context contains index bounds, list-length facts, loop guards, branch conditions, `@pre` bridges, and array-read bindings. Missing facts require annotation or vc-checking repair.

A common order for pure goals is:

```coq
split_pures.
- dump_pre_spatial. subst. lia.
- dump_pre_spatial. rewrite Zlength_app. rewrite Zlength_cons. lia.
- dump_pre_spatial. eapply some_case_helper__gid; eauto.
```

For list equalities, first try existing `sublist`, `replace_Znth`, and `Zlength` lemmas. When a stable bridge is missing, add it to `group_worker_lib` with a name ending in the current group suffix.

## Array and string goals

A typical array proof derives `Zlength` from `full` / `seg`, splits at the current index, merges back to `full` / `seg` after the write, and proves list relationships with pure lemmas for `replace_Znth`, `sublist`, and `Znth`.

A typical string proof unfolds `store_string`, `c_string`, or `string_length`, handles the terminating zero, and distinguishes a Rocq `string` from `list Z`.

When a helper lemma is needed, add and prove it in `group_worker_lib`; never add it to `*_proof_manual.v`.

## Whole-proof skeleton

A common entailment proof is:

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

If `cancel P` does not match, first check whether both sides are syntactically identical. `cancel` does not normalize resources that are semantically equal but syntactically different. First rewrite pure equalities, normalize list expressions, or use `sep_apply_*_atomic` to change resource shape.

## Failure signals

Prefer a proof/helper change when:

- The goal is list arithmetic or a bridge involving `sublist`, `replace_Znth`, `Permutation`, or bounds.
- A spatial resource needs a known split/merge lemma.
- The annotation already exposes every necessary bound and branch fact.

Prefer returning to annotation when:

- The premise lacks the current index bound, branch condition, array-read binding, or `@pre` bridge.
- A heap resource needed by the postcondition has already disappeared from the precondition.
- A functional fact required by the witness statement never appears in the invariant or `Ensure`.
