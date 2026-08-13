# Refinement-Proof Rules

This document records stable proof patterns for `safeExec` goals in refinement VCs.

## Skeleton

```coq
(* For a top-level VC, use exactly the controller-verified mode from the handoff. *)
LLM_pre_process ltac:(lia || int_auto). (* shown only for an LLM_pre_process route *)
(* 1. Choose postcondition witnesses. *)
Exists ... .
(* 2. Perform necessary spatial simplification. *)
simpl ... .
(* 3. Split spatial and execution goals first. *)
split_pure_spatial.
- (* spatial side *)
  ...
- (* safeExec side *)
  unfold wrapper_name in H at 1.
  prog_nf in H.
  unfold_loop in H.
  prog_nf in H.
  safe_choice_l H.  (* or safe_choice_r H *)
  ...
  exact H.
```

## Mandatory rules

1. A top-level VC never chooses between modes locally. If the handoff says `LLM_pre_process`, use `LLM_pre_process ltac:(...)` and leave its split-goal `Abort.` blocks unchanged. If it says `aggressive_pre_process`, first complete every assigned split goal according to its strategy, then use `aggressive_pre_process.` in the top-level VC and run only `Goal_apply <corresponding split-goal lemma>.` on each resulting branch. Do not replace `Goal_apply` with `apply`, `eapply`, `exact`, `refine`, or a local alias. This is a worker rule, not a controller tactic-text check. These modes select respectively the original and strategy-processed branches of `original VC \/ strategy-processed VC`.
2. Choose witnesses before `split_pure_spatial`.
3. Do not unfold a `safeExec` wrapper before `split_pure_spatial`.
4. Solve the spatial side before the execution side.
5. On the execution side, follow every `unfold ... in H at 1` or `unfold_loop in H` with `prog_nf in H`.
6. When the normalized hypothesis matches the goal, use `exact H`.
7. When the hypothesis contains a `choice`, select the matching branch with `safe_choice_l H` or `safe_choice_r H`.

## Permitted unfolding

For a goal `safeExec ?P prog X`:

- If goal-side `prog` is a direct wrapper application, it may be unfolded in the goal.
- If `prog` is already a compound expression such as bind, choice, or loop, prefer unfolding in the hypothesis.
- If wrapper names are definitionally equal but do not syntactically match, use `change` to align the names, then `exact H`.

For goals other than `safeExec`, use ordinary tactics such as `unfold`, `simpl`, `lia`, and `congruence` normally.

## Working with `safeExec`

After isolating a `safeExec` goal, find the hypothesis carrying the current execution fact, usually of this shape:

```coq
H : safeExec ATrue (some_wrapper args) X
```

Normalize only that hypothesis:

```coq
unfold some_wrapper in H at 1.
prog_nf in H.
```

For a loop combinator:

```coq
unfold_loop in H.
prog_nf in H.
unfold loop_body in H at 1.
prog_nf in H.
```

When the normalized hypothesis matches the goal:

```coq
exact H.
```

When the hypothesis contains a `choice`, use the current branch fact to choose a direction:

```coq
safe_choice_l H.  (* or safe_choice_r H *)
- exact H.
- lia.            (* assume!! side condition, ordinary Rocq proposition *)
```

Guard goals created by `safe_choice_l/r` are ordinary Rocq propositions, not `safeExec` goals. Solve them with `unfold`, `simpl`, `lia`, `congruence`, or case-specific helpers.

## Goal-side unfolding

Unfold in the goal only when the goal program is a direct wrapper application:

```coq
change (safeExec P (wrapper2 args) X).
unfold wrapper2.
prog_nf.
```

If the goal is already a `bind`, `choice`, `repeat_break`, or other compound program, operate on the hypothesis instead. Do not use `unfold ... in *` simultaneously on the goal and hypothesis; it destroys program shapes that otherwise match.

When names differ but are definitionally equal, align them with `change`:

```coq
change (safeExec P (old_name args ;; rest) X).
exact H.
```

## Forbidden patterns

Do not use these low-level reconstruction patterns:

- `safeExec_bind_reta`
- `safeExec_bind`
- Manually constructing a new `assert (Hs : safeExec ...)`.
- `unfold ... in *` on `safeExec`-related definitions.
- Manually reassociating binds when `prog_nf` can do it.

In particular, do not invent this to prove the execution side:

```coq
assert (Hs : safeExec P prog X).
```

Do not rebuild bind, return, or choice manually with low-level lemmas. The generated VC normally already contains the correct execution hypothesis. Unfold its current wrapper, run `prog_nf in H`, choose the branch, and use `exact H`.

## Diagnosing failure

If the abstract program state still cannot align with the goal after `prog_nf in H`, `unfold_loop in H`, and the correct `safe_choice_l/r`, suspect an annotation/specification error before stacking more tactics.

Check in this order:

1. Was the wrong witness selected, producing the wrong abstract-state tuple in the postcondition?
2. Has the spatial side not yet reshaped resources as the goal needs?
3. Does the branch fact point to the other side of the `choice`?
4. Does the loop-state tuple agree with the `safeExec` residual in the annotation invariant?
5. Is the current VC premise missing a pure fact that annotations should provide?

If only a wrapper name, list expression, or arithmetic guard differs, add a proved current-suffix helper to `group_worker_lib` or adjust the proof. Do not return `blocked` merely because the proof route is uncertain.
