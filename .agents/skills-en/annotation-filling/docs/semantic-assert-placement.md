# Semantic Assert Placement

This document explains where to place ordinary `Assert` blocks in QCP C annotations. The goal is not to minimize assertions mechanically. It is to keep C files readable while using a small number of stable semantic cut points to control symbolic-execution paths and the shape of later VCs.

## Default structure

- Use a stable `Inv Assert` at the loop head to state variable ranges, spatial resources, and the core mathematical relationship between processed and unprocessed portions.
- Do not treat an ordinary `Assert` as a mandatory step after every `if` or assignment; retain it only when it has a clear connection role.
- Prefer function specifications, loop invariants, and existing separation-logic rules for facts they can express naturally.

## Where an ordinary `Assert` is useful

An ordinary `Assert` should serve at least one of these roles:

- **Function-call boundary**: organize the current state into the callee's `Require`, or explicitly recover the caller's abstract state after the call.
- **Semantic-phase transition**: move from one stable domain state to another, for example from a “frontier maximum” to an “inclusive maximum.”
- **Path join**: several upstream paths establish the same domain property, and complex branching, a function call, or a long common suffix remains downstream; the assertion lets later symbolic execution forget irrelevant path history.
- **Exit bridge**: the transformation from the loop-exit state to the function's `Ensure` is itself an important, reusable mathematical step. Omit this assertion when the return point can derive `Ensure` directly from the invariant.

For a semantic-phase transition or path join, prefer a named domain predicate such as `PhaseSummary` over a copied list of low-level arithmetic facts. The domain predicate must describe a mathematical property or stable local observation; it must not rewrite the C loop body as a Rocq state machine.

## Ordinary `Assert` blocks to remove

- A loop-body entry assertion that copies the complete `Inv Assert` and adds only the loop guard.
- A branch-end assertion immediately before the loop back edge that merely restates the next-iteration invariant.
- An assertion after a simple assignment that repeats an equality or range already implied directly by the symbolic state.
- An assertion before return that copies the function's `Ensure` without a distinct mathematical exit step.
- An assertion added only to suppress a temporarily unprovable VC and lacking stable semantic meaning.

Removing an ordinary `Assert` does not remove the mathematical obligation. If the assertion was only a relay point, the obligation moves to loop preservation, a function call, or a return witness. Compare the resulting VC structure rather than only the number of C lines or whether a VC still exists.

## Qualitative path-convergence test

At a candidate location, ask:

1. Are there already multiple upstream paths, for example from consecutive conditional updates?
2. Does the downstream code still contain complex branching, function calls, or a long common suffix?
3. Can the upstream paths jointly establish a domain predicate more stable than each concrete symbolic state?
4. After adding the assertion, can the downstream proof depend only on that domain predicate rather than concrete path history?

If most answers are yes, the ordinary `Assert` is usually a useful semantic cut point. Do not require an exact path count; path products are only a signal for potential VC blow-up. If the assertion is followed immediately by the loop head or a return, the loop invariant or function `Ensure` is usually already the natural join point.

## Relationship to Rocq helper lemmas

- For a stable semantic cut point, prefer a phase-transition lemma such as `LoopState -> StepState`.
- Different successors such as left and right branches may use separate branch-progress lemmas.
- Consider a full-iteration lemma only when several witnesses genuinely repeat the whole derivation.
- Do not require a fixed statement for a full-iteration lemma or a fixed tactic template for manual witnesses.
- A manual witness should carry only VC-specific instantiation, path conditions, and spatial connection. Extract mathematical reasoning that is genuinely reusable across witnesses into helper lemmas.

A Rocq helper can shorten a witness, but it cannot retroactively merge symbolic-execution paths that have already been expanded. Semantic `Assert` blocks and helper lemmas are therefore complementary, not mechanically interchangeable.

## Review record

For every ordinary `Assert`, record the following in the current attempt's `agent_output.md`; if no ordinary `Assert` exists, explicitly record `none`:

```text
location:
purpose: one or more of function-call-boundary | semantic-phase-transition | path-join | exit-bridge
named_semantic_state: predicate name | none
upstream_paths: qualitative description
downstream_work: qualitative description
redundant_with_invariant_or_postcondition: yes | no
decision: keep | remove | revise
rationale:
```

`upstream_paths` and `downstream_work` need only qualitative descriptions; they do not require a formal proof for every path. One assertion may serve several roles. For a function-call or resource-connection assertion with no suitable domain predicate, `named_semantic_state` may be `none`. If no connection role can be explained, or the assertion duplicates an invariant or postcondition, prefer removal or revision.

## Comparison examples

- In `QCP_examples/LLM_bench/Algorithms/rmq/rmq.c`, the table-building loop establishes `STLevelPrefix(..., i + 1)` after two write branches, joining different paths into one mathematical state.
- In `QCP_examples/LLM_bench/Algorithms/quicksort_lomuto_index/quicksort.c`, the partition scan uses `partition_scan_inv` as its loop-head semantics. When a branch returns immediately to the loop head, prove invariant preservation directly rather than mechanically adding an ordinary `Assert` for every branch.

These examples compare the connection role of assertions only. They do not imply that the existing specification, helper layout, or formal-file structure should be copied verbatim.
