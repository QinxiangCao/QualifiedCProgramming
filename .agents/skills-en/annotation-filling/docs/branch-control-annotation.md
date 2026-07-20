# Branch-Control Annotation Guide

This document explains how the annotation subagent should use branch-control features to manage multiple symbolic-execution states while writing annotations. It records both the current branch-control syntax and repository annotation practices and is intended to be usable on its own.

## When to use branch control

Prefer branch control over one enormous `Assert` / `Inv Assert` that attempts to absorb every case when the C program has any of these forms:

- Different paths preserve different pure facts after a branch, such as `x == 0` versus `x > 0`.
- A loop entry has distinct phases or boundary cases, such as `n == 0` and `n > 0`.
- Some paths have become impossible and should be removed explicitly.
- Several paths have the same later semantics and should be merged explicitly.
- A subset of branches needs a case split that should not affect other branches.

The core principle is to name semantically different paths first, then apply assertions or invariant transformations only to the target branches. Join paths only when their semantics genuinely converge.

## Branch names

`Branch name` names current branches by condition:

```c
/*@ Branch name
    zero: x == 0;
    positive: x > 0
*/
```

When only one branch exists at the current point, use the short form:

```c
/*@ Branch name entry */
```

Rules:

- `all` and `unnamed` are reserved and cannot be ordinary names.
- Naming replaces an old name.
- One name may refer to several branches.
- If a named branch later splits naturally, its children inherit the name.
- The tool reports an error if a name's condition matches no branch; do not probe with an uncertain condition.

## `$ branch_list`

Many annotations accept `$ branch_list` to select their scope:

```c
/*@ Assert x >= 0 $ zero positive */
/*@ x >= INT_MIN by local $ normal */
```

Rules:

- With `$ branch_list`, only the selected branches are transformed; unselected branches remain unchanged.
- Omitting `$ branch_list` is equivalent to `$ all`.
- `all` selects every current branch, and `unnamed` selects unnamed branches.
- `$` is not used to select cases for ordinary `Inv`; loop-case selection uses the multi-invariant case/direct mechanism.

When a local fact holds only during one phase, write the `$` selector explicitly so it is not incorrectly required on other branches.

## Grouping semantics of `Assert`

In the current version, an `Assert` without `$` does not indiscriminately merge every branch. It operates on groups determined by the current branch name:

```c
/*@ Branch name zero: x == 0; one: x == 1 */
/*@ Assert x >= 0 */
```

The `zero` and `one` groups are each checked and replaced with `x >= 0`, while retaining their names. Unnamed branches form a separate unnamed group.

If the assertion itself branches, such as `P || Q`, each name group separately splits into `P` and `Q` result branches, and those branches inherit the group's name.

Use this behavior to retain case information. If several differently named branches should truly become one state, use `Branch join` explicitly.

## `Destruct`

`Destruct` performs a case split on selected branches:

```c
/*@ Destruct $ all with
    zero: n == 0;
    normal: n > 0
*/
```

When several source branches are selected, every destruct case must provide a new name for every source branch:

```c
/*@ Destruct $ zero one with
    zero_low one_low: x < 10;
    zero_high one_high: x >= 10
*/
```

The tool generates a coverage check for each source branch: the original assertion must imply the disjunction of all destruct conditions. `Destruct` is not a free case split; current branch semantics must cover its conditions.

References:

- `QCP_examples/QCP_demos_tutorial/branch_destruct.c`
- `QCP_examples/QCP_demos_LLM/bubble_sort.c`

`bubble_sort.c` first uses `Destruct $ all` to split `n == 0` and `n > 0` into `zero` and `normal`, then gives the outer loop a case invariant for each. The zero-length case therefore does not have to satisfy facts such as `1 <= n` or `0 <= i <= n - 1`, which apply only to the normal case.

## `Branch clear`

`Branch clear` removes named impossible branches:

```c
/*@ Branch clear zero */
/*@ Branch clear unnamed */
/*@ Branch clear all */
```

Rules:

- The tool checks that each removed branch's assertion entails a contradiction.
- It deletes the branch directly when it can prove this automatically; otherwise it generates a proof obligation.
- The current implementation warns if the selector matches no branch.

A common use is to remove a phase that can no longer execute after a multi-invariant or an if/else. Do not use `Branch clear` to hide a genuinely reachable path. If it cannot be cleared, recheck the precondition, branch condition, and name.

Reference:

- `QCP_examples/QCP_demos_tutorial/multiinv_examples.c`

## `Branch join`

`Branch join` merges selected branches:

```c
/*@ Branch join zero one into both with x >= 0 */
/*@ Branch join zero one into both with Assert x == 0 || x == 1 */
```

When the expression after `with` is a partial assertion:

- The tool partially solves each selected branch.
- Frames for the merged branches must align.
- The result must be one non-branching branch.
- With `into both`, the result is named `both`; otherwise it is unnamed.

When the expression after `with` is a full `Assert`:

- The join result is exactly the contents of `Assert`.
- `Assert` may be branching, such as `P || Q`.
- With `into both`, every result branch produced by `Assert` is named `both`.
- Unselected branches remain unchanged.

When the two sides of an if/else perform different assignments but later reasoning needs only one common abstract fact, prefer `Branch join` to extract it. For example:

```c
/*@ Branch join all with x == step(x@pre) */
```

Reference:

- `QCP_examples/QCP_demos_tutorial/branch_join_private_condition.c`

## `Inv Assert` and ordinary `Inv`

`Inv Assert` is a full invariant and uses the same branch-name grouping semantics as `Assert`:

```c
/*@ Branch name zero: x == 0; one: x == 1 */
/*@ Inv Assert x >= 0 */
while (x >= 0) {
  ...
}
```

Ordinary `Inv` is a partial invariant. It partially solves a frame for each case and reuses the resulting full invariant whenever control later reaches that case again.

A multi-invariant uses case names for loop phases:

```c
/*@ Inv
    zero:
      n == 0 && inv_zero;
    normal:
      n > 0 && inv_normal
    with
    zero ==> zero
    normal ==> normal
*/
while (...) {
  ...
  /*@ normal ==> normal */
}
```

Rules:

- Without an explicit direct target, a named branch tries to enter the invariant case having the same name.
- An explicit `pre ==> case` mapping overrides the default match.
- When several branches enter one case, they are effectively joined/solved against that case invariant first.
- A branch that may enter the loop but matches no invariant case is an error.
- A branch that definitely cannot enter the loop may flow directly after the loop and does not need an invariant case.
- Explicitly directing the same branch to multiple distinct cases is an error.

References:

- `QCP_examples/QCP_demos_tutorial/multiinv_examples.c`
- `QCP_examples/QCP_demos_LLM/bubble_sort.c`

`bubble_sort.c` demonstrates both forms: one writes `with zero ==> zero; normal ==> normal` explicitly, and the other relies on named branches entering same-named cases. For new annotations, prefer an explicit `with` mapping when the case relationship could be misread.

## Branch names in `which implies`

`which implies` supports input and output branch names:

```c
/*@ pre $ a b
    which implies
    post $ a1 a2 b1 b2
*/
```

If each input branch splits into several outputs, the output names correspond to the new branches in generation order. Ensure the number of output names matches the actual number of results and explain in the report how the names map to semantic paths.

## Selection strategy

- Preserve path differences with `Branch name` or `Destruct`.
- Add facts only to certain paths with `$ branch_list`.
- Remove impossible paths with `Branch clear`, after confirming the contradiction is semantically real.
- Turn several paths into one common fact with `Branch join`.
- For loops with phases or boundary cases, use named branches and multi-invariant cases, with explicit `==>` mappings when needed.
- If all branches are isomorphic and only a complete loop state is needed, use `Inv Assert`, remembering that it still groups by branch name.

## Common mistakes

- Using `all` or `unnamed` as an ordinary name.
- Omitting `$ branch_list` and accidentally requiring a local fact on every branch.
- Assuming an unnamed `Assert` merges all branches; the current version groups by branch name.
- Using a partial-assertion `Branch join` to produce a branching assertion; use `with Assert ...` when the result must branch.
- Selecting several source branches in `Destruct` but providing only one new name per case.
- Naming loop-entry branches whose names do not match multi-invariant cases, without an explicit `with pre ==> case` mapping.
- Using `Branch clear` on a reachable path and turning later VCs into an annotation bug.

## Note requirements

If the current annotation uses branch control, briefly record in `agent_output.md`:

- The branch names and the semantic path each represents.
- Which annotations use `$ branch_list` and why they apply only to those branches.
- Whether `Destruct`, `Branch clear`, or `Branch join` was used, together with the corresponding coverage, contradiction, or common fact.
- The multi-invariant case/direct mapping, especially which branches enter same-named cases by default and which use explicit `==>` mappings.
- Whether these branch-control decisions may affect witness structure or later manual VCs.
