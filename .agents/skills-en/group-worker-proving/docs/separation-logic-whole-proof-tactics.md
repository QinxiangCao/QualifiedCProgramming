# Separation-Logic Proof Rules

This document records common proof patterns for generated manual VCs of the form `P |-- Q`.

## Basic workflow

Every top-level VC must use only the controller-verified route from the handoff. `LLM_pre_process ltac:(...)` is the whole-goal route; `aggressive_pre_process.` is the route where strategies generated split goals that this group proves first. Both unfold the VC, introduce variables, and extract some pure facts.

## Required skeleton

Only two proof openings are legal, fixed by the kind of declaration:

Top-level VC with usable split goals (`aggressive_pre_process` route):

```coq
Proof.
  aggressive_pre_process.
  - Goal_apply <vc>_split_goal_1.
  - Goal_apply <vc>_split_goal_2.
Qed.
```

Split goals, and any top-level VC that must be proved whole (`LLM_pre_process` route):

```coq
Proof.
  LLM_pre_process ltac:(<closer>).
  ...
Qed.
```

Hard requirements:

- After `aggressive_pre_process.`, only `Goal_apply <corresponding split-goal lemma>.` is allowed, one per branch, with no other tactic. The top-level proof is a dispatch layer and nothing else.
- Every split goal must open with `LLM_pre_process ltac:(...)` and spell out its closer, normally `ltac:(lia || nia || int_auto)`.
- The alias `pre_process` is forbidden. It is exactly `LLM_pre_process ltac:(lia || nia || int_auto)` (`CommonAssertion.v`), but it hides the closer, so it must not appear in proof text.
- Do not substitute a hand-written `unfold <goal_name>.` + `intros ...` for `LLM_pre_process`.

The current symbolic-execution printer may produce the final VC as:

```coq
original_vc \/ vc_after_strategies
```

`LLM_pre_process` selects the original branch internally, while `aggressive_pre_process` selects the strategy-processed branch. Do not write `left;` or `right;` before either tactic.

Generated `<vc_name>_split_goal_*` declarations are not disposable diagnostics:

- When the handoff selects `aggressive_pre_process`, they are assigned formal subgoals. Edit only each proof span, open it with `LLM_pre_process ltac:(...)` per the required skeleton above, and complete it with `Qed.`. Then run `aggressive_pre_process` in the top-level VC and use only `Goal_apply <corresponding split-goal lemma>.` on each resulting branch. Do not replace `Goal_apply` with `apply`, `eapply`, `exact`, `refine`, or a local alias. Apart from the forbidden tactics, which the controller scans, the skeleton is a worker rule and not a controller tactic-text check.
- When the handoff selects `LLM_pre_process`, prove only the top-level whole goal. The generated split goal is outside this route and must retain the Rocq tokens `Proof. Abort.`. Do not complete it opportunistically. Comments, whitespace, CRLF/LF, and the EOF newline do not affect this check.

Never change the route locally. If the controller-verified route reveals a semantic gap in the current proof state, record that concrete state and block/return to annotation.

## Proof reuse hint

If the group handoff provides `proof_reuse.md`, read the referenced previous current-run files and exact line ranges in the strict order: all helper rows, all aggressive split-goal rows, then all `LLM_pre_process` top-level rows. An aggressive top-level VC has no reuse row. Every non-from-scratch range covers the entire parser-recognized declaration rather than a few tactic lines inside it. A sealed source may be a failed proving round or a verified round made stale by annotation/freshness retry; structurally invalid failed groups have already been omitted. Helper/proof `direct copy` comes only from a previously controller-validated accepted group. Direct manual proof also requires matching generated-goal semantic fingerprints, permitting only a generated-declaration rename. An unaccepted source proof provides at most `partial proof-idea reuse`, and its helper must be rebuilt from scratch. Recheck every candidate against current binders, hypotheses, and proof mode. When a fingerprint changed, rebuild the adapter/frame described by the hint or start from scratch. The hint never permits modifying previous files, never replaces current debug/development/exact checks, and must not trigger a historical scan when the handoff says none.

When a split goal changes from `P |-- Q` to `P' |-- Q'`, first try wrapping the old proof in two adapters: prove `P |-- P'` to enter the old precondition, then prove `Q' |-- Q` to return to the new conclusion. If the change only adds, removes, or reorders a common spatial frame, use an explicit cancellation/frame transformation and discharge its side conditions. These are `partial proof-idea reuse`, not verbatim direct copy. The Reason is a design hint only; this group must prove the actual adapter. A single-witness group should use its helper/split components from the hint. A multi-witness group must not assume one group helper mechanically serves every witness.

A typical aggressive route completes split declarations before the top-level declaration:

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

Use the current proof state and handoff—not the example—to determine subgoal count, arguments, and `Goal_apply` order. A split-goal proof body may still use other tactics and ordinary mathematical helpers. The restriction concerns only how an aggressive top-level VC applies its assigned split lemmas.

## `Intros` / `Intros_p`

- `Intros x.` introduces an `EX x` from the precondition.
- `Intros x y.` introduces several existential witnesses in sequence.
- `Intros_p H.` introduces a pure fact `[| P |]` from the precondition.

If unnamed existentials or pure facts remain in the proof state, introduce them explicitly before using `cancel`, `sep_apply`, or arithmetic.

## `Exists`

Use `Exists x.` or `Exists x y.` to instantiate postcondition existentials. Choose values from vc-checking's witness plan, such as the old logical list, `replace_Znth(i, v, l)`, `sublist(lo, hi, l)`, `l ++ [v]`, or the current abstract state.

Do not postpone existential choices until the spatial goal has become complicated.

## `cancel`

`cancel P.` removes spatial resources that are syntactically identical in pre- and postconditions. If resources are only arithmetically equivalent, first rewrite or normalize them using pure facts. When the goal becomes `P |-- P`, `cancel P` usually closes it.

## `sep_apply_l_atomic` / `sep_apply_r_atomic`

- `sep_apply_l_atomic (Lemma args).` transforms a precondition resource into the lemma's conclusion shape.
- `sep_apply_r_atomic (Lemma args).` expands a postcondition resource into the lemma's premise shape.

Instantiate lemma parameters explicitly. Pure-premise side goals must be discharged by facts exposed by the current annotations.

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

Never temporarily `admit` a necessary pure premise or change the witness statement. If the premise is absent from the current VC, check for a missing annotation branch fact, bound, array-read binding, or `@pre` bridge.

## `prop_apply_p`

`prop_apply_p (Lemma args premises).` derives a new pure fact from precondition resources through a separation-logic lemma and adds `[| R |]` back to the precondition.

Use it to:

- Derive non-null, length, shape, or segment relationships from list/structure predicates.
- Export a side condition before `sep_apply_*`.
- Expose a current spatial resource as a pure hypothesis for arithmetic or list reasoning.

Instantiate every parameter and premise explicitly. If a premise cannot be proved from the current context, do not fabricate it; return to annotation or add a helper bearing the current group suffix. A sealed helper from the handoff's frozen snapshot may retain its historical suffix when its declaration/proof tokens match; a substantively modified version must use the current suffix.

## Disjunction and universal quantification

- `Left.` proves the left side of `P |-- Q || R`.
- `Right.` proves the right side of `P |-- Q || R`.
- `Split.` turns `P || Q |-- R` into two goals.
- `Intros_r x.` introduces an `ALL x` from the postcondition.

Before choosing `Left` or `Right`, inspect the branch fact, loop guard, or constructor shape. Do not pick an arbitrary branch merely to advance the script; a wrong branch usually leaves an impossible pure goal.

## Pure-goal tools

`split_pures.` splits several pure postcondition conjuncts into separate goals.

`dump_pre_spatial.` discards the precondition's spatial part and changes `P |-- [| Q |]` into an ordinary Rocq goal `Q`. Use it only after introducing every required pure fact.

## Handling pure goals

A common flow is:

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

`entailer!` is a forbidden tactic and must not appear in proof text. Internal calls from `LLM_pre_process` and `Goal_apply` are unaffected.

`lia` is not a proof plan. First ensure the context has index bounds, list-length facts, loop guards, branch conditions, `@pre` bridges, and array-read bindings. Missing facts require annotation or vc-checking repair.

A common order for pure goals is:

```coq
split_pures.
- dump_pre_spatial. subst. lia.
- dump_pre_spatial. rewrite Zlength_app. rewrite Zlength_cons. lia.
- dump_pre_spatial. eapply some_case_helper__gid; eauto.
```

For list equalities, first try existing `sublist`, `replace_Znth`, and `Zlength` lemmas. When a stable bridge is missing, put a new helper in `group_worker_lib` with the current group suffix. A public/reuse helper may retain its source suffix when its sealed declaration/proof tokens match.

## Array and string goals

A typical array proof derives `Zlength` from `full`/`seg`, splits at the current index, merges back to `full`/`seg` after the write, and proves list relationships using pure `replace_Znth`, `sublist`, and `Znth` lemmas.

A typical string proof unfolds `store_string`, `c_string`, or `string_length`, handles the terminating zero, and distinguishes a Rocq `string` from `list Z`.

When a helper lemma is needed, add and prove it in `group_worker_lib`; never put it in `*_proof_manual.v`. At turn start, browse only the handoff's round-start frozen public snapshot and copy useful proved declarations with identical declaration/proof tokens plus necessary official imports into the local library. Never import or edit the snapshot/durable pool directly. A copied candidate may remain unused, but it must still pass this group's check.

## Whole-proof skeleton

A common entailment proof is:

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

If `cancel P` does not match, first check whether both sides are syntactically identical. `cancel` does not normalize resources that are semantically equal but syntactically different. Rewrite pure equalities, normalize list expressions, or use `sep_apply_*_atomic` to change resource shape first.

## Failure signals

Prefer a proof/helper change when:

- The goal is list arithmetic or a bridge involving `sublist`, `replace_Znth`, `Permutation`, or bounds.
- A spatial resource needs a known split/merge lemma.
- The annotation already exposes all required bounds and branch facts.

Prefer returning to annotation when:

- The premise lacks the current index bound, branch condition, array-read binding, or `@pre` bridge.
- A heap resource needed by the postcondition has already disappeared from the precondition.
- A functional fact required by the witness statement never appears in the invariant or `Ensure`.
