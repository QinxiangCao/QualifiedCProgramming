# Ordinary Assert Placement

Use an ordinary `Assert` only for state that verification needs but symbolic execution cannot determine at that program point. The plan does not duplicate ordinary assertions; the C annotation is authoritative.

## Placement rules

- Put an `Inv Assert` before every loop, describing progress, live resources, and stable mathematical state.
- Do not stack an ordinary `Assert` immediately before an `Inv Assert`.
- An ordinary `Assert` may appear before an `if`, but only when the branch test or branch verification genuinely lacks needed state.
- Never put an ordinary `Assert` before a `return`; connect the loop-exit or current symbolic state directly to `Ensure`.
- Elsewhere, add one only when the program state truly cannot be determined and verification depends on the missing information.

Do not replace these rules with `by local`, branch control, ordinary `Inv`, multi-invariants, or call `where` clauses in function bodies.

## Keep assertions short

An ordinary `Assert` contains only facts and resources actually used downstream. Remove assertions that:

- copy the following `Inv Assert`;
- repeat the symbolic state after a simple assignment;
- restate the invariant at a branch end only to return to the loop head;
- copy `Ensure` before a return;
- have no program meaning and exist only to suppress a VC temporarily.

When a fact follows directly from the specification, current guard, existing resources, or loop invariant, let symbolic execution use it without another ordinary `Assert`.
