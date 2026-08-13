# Predicate-First Annotation

This document deepens the spec-first and predicate-first design discipline in `annotation-guide.md`. It specifically blocks a common pattern that must not continue to spread:

- First redefine the C algorithm in Rocq.
- Then make the C annotations and later proofs track that Rocq algorithm mirror.

This pattern weakens the annotations by deferring runtime properties that belong at the C level to Rocq proofs. It also forces VCs to revolve around an “algorithm interpreter” and creates unnecessary cascading invalidation whenever C control flow or annotations are revised.

## Default principles

- Use predicate-first annotations by default for direct proofs, starting with the local hidden properties a human would state first.
- A refinement proof may retain the `safeExec` / monadic specification required by its proof type, but local loop state, prefix/suffix relationships, processed intervals, and candidate optima should still be stated directly by the C annotations wherever possible.
- First confirm that the target specification in `formal_case_lib` is a rigorous mathematical property, then make the C annotations invoke it. If the specification is missing, too strong, too weak, or an algorithm mirror, repair the specification before adjusting the annotations.

In one sentence: state the local runtime semantics as predicates before deciding which helper lemmas are needed; do not begin by writing a Rocq algorithm.

## What is a hidden property?

A hidden property does not rewrite code in another language. It extracts the mathematical fact that each loop iteration truly maintains. Typical forms include:

- Processed prefix / unprocessed suffix.
- Merged prefix / left and right pending intervals.
- Current candidate optimum or feasibility boundary.
- A suffix, prefix, or subarray property at a boundary.
- Written prefix plus unwritten or uninitialized suffix.
- Permutation / sorted / bounded / shape-preserved.

These properties should appear first in `Require`, `Ensure`, `Assert`, and `Inv Assert`, rather than being hidden first inside a new Rocq recursive algorithm definition.

## Positive and negative examples

### Negative example: algorithm mirror

Read `incorrect-examples/algorithm-mirror.md`, followed by `max_sub_array.c`, `max_sub_array_lib.v`, and `max_sub_array_goal.v` in the same directory. The example first defines a recursive interpreter that follows the Kadane-style C loop and then makes the specification and invariant track that interpreter. It replaces the properties that should be stated directly—such as the maximum suffix and maximum subarray of the current prefix—with an algorithm-synchronization relation.

The problem is not that the recursive definition cannot be written. The problem is that it hides the mathematical meaning of the current program point inside another program.

### Positive example: majority element

`QCP_examples/LLM_bench/Algorithms/majority_element/majority_element.c` uses small, intuitive property interfaces such as `IsMajorityElement` and `MajorityOnReduced`. Its loop invariant directly states the relationship among the current `vote`, `candidate`, remaining list, and global majority element. The definitions describe properties rather than reproducing Boyer-Moore control flow.

### Positive example: binary answer

`correct-examples/binary-search-annotation.md` and the accompanying `split_array_largest_sum/` materials demonstrate the design for “binary search on the answer plus a check function”:

- The `check` function's `Ensure` exposes the `CanSplit` / `CannotSplit` decision semantics.
- The main-loop invariant keeps the true mathematical answer in `[left, right]`.
- Proof helpers connect feasibility decisions to optimal-value bounds without defining the binary-search process as a Rocq program.

## Prefer explicit witness representations

When designing a `formal_case_lib` specification, do not wrap a finite result uniquely determined by its input in a higher-order existential witness such as `exists f : Z -> Z, ...` without a reason. Doing so expands the later proof search space: the worker must guess a lambda, values outside the valid domain, the notion of pointwise equivalence, and whether functional extensionality or choice is needed.

Choose a representation in this order:

1. When the witness is uniquely determined by the input and has a clear mathematical closed form, prefer a transparent canonical value.
2. When the witness is a sequence over a finite contiguous interval and the proof mainly uses length, indexing, prefixes/suffixes, or segmentation, prefer a list with a `Zlength` constraint.
3. Retain an existential function only when the mathematical object is inherently a function or an existing functional algebraic interface materially simplifies later proofs.

A transparent canonical value or list profile must still describe a mathematical object; it must not become another way to rewrite the C loop body. `exists f` is not itself a choice axiom and is not categorically forbidden. If an existential function is retained, explain its domain, valid range, concrete advantage over a canonical value or list, and whether a transparent constructor or construction lemma already exists, so proof workers do not repeat the same witness search.

For example, when every derived value at an index of a finite array is uniquely determined by the input, prefer a direct canonical definition or a result list with the same length as the input rather than defaulting to `exists value_at : Z -> Z, ...`. Naturally mapping-shaped objects such as graph colorings, vertex potentials, and variable assignments may remain function witnesses.

## What to learn from existing cases

Useful references include:

- `QCP_examples/QCP_demos_LLM/int_array_merge_rel.c`
- `QCP_examples/QCP_demos_LLM/sll_merge_rel.c`

Study how they organize interval decomposition, processed progress, and pure/spatial/`safeExec` information side by side. Reuse only the annotation style; do not copy another case's proof scripts, generated artifacts, or formal-file structure.

## Allow, scrutinize, and block

Allow:

- Small property interfaces such as `subarray_sum`, `suffix_sum`, `prefix_sum`, or a simple optimality predicate.
- Small mathematical lemmas that connect annotation steps.
- The `safeExec` / monadic specifications required by a refinement proof.

Scrutinize:

- A new definition that begins to reproduce loop locals and state transitions one for one.
- An invariant whose core semantics depend on running a Rocq algorithm first.
- Proof work that becomes synchronization between a Rocq algorithm and the C algorithm rather than reasoning about local annotation properties.

Block:

- Introducing an algorithm-mirror `Fixpoint` or state machine in a direct proof solely because the annotations did not state the local property.
- Writing annotations as projections of a Rocq algorithm definition rather than explanations of runtime program state.

## Design review

Before writing or restructuring annotations, answer in order:

1. Which mathematical input/output relationship must the function's `Ensure` state?
2. Which local fact does every iteration of each loop actually maintain?
3. Can those facts be expressed as prefix, suffix, segment, shape, or optimality predicates?
4. If a new definition is needed, does it describe an independent mathematical property or replay the algorithm?
5. Should a failed proof be repaired with a helper lemma connecting existing properties, or does it reveal that the annotation itself is inadequate?
6. If the specification uses an existential function, could a canonical value or finite list state the same witness more explicitly and reduce later search?

If the answer to question 4 is close to “replay the algorithm,” immediately return to specification and annotation design rather than handing the candidate to later VC proving.
