---
name: annotation-designing
description: Use when the controller delivers an initial annotation attempt or appends failed VCs; the same annotation owner derives a mathematical specification from the problem, reuses core predicates, writes minimal function contracts and loop invariants, and repairs symexec failures in the current attempt.
---

# Annotation Design and Authoring

One annotation owner handles the initial attempt and every retry in the main root.

Work in this order:

    problem statement
      -> natural-language specification
      -> Rocq specification
      -> C function contract
      -> loop invariant
      -> symexec

The natural-language specification, Rocq Spec, and C Ensure state the same output relation. Editorials, algorithm hints, loop state, DP transitions, and data-structure construction do not belong in the top-level specification.

Before writing a definition, search the current dependencies, canonical case library, and shared libraries. Directly combine existing predicates such as Zlength, Znth, sublist, replace_Znth, Forall, Forall2, In, NoDup, Permutation, sum, and the existing monotonicity, extrema, path, and array predicates. Do not add successive wrappers around those combinations. When the problem meaning or a cross-function interface needs a name, keep one case predicate and refer to it directly everywhere else.

Expand input ranges, element ranges, and overflow conditions in the function contract. Use With for logical values, Require for entry conditions and resources, and Ensure for the mathematical result and returned resources.

Put one Inv Assert before every loop. It contains only mathematical progress, ranges needed by the next execution step, live resources, and necessary @pre bridges. Use an ordinary Assert only when symbolic execution cannot recover state needed downstream; it may appear before an if, but not before a return or an Inv Assert. Do not use by local, branch control, ordinary Inv, multi-invariants, or call where clauses in a function body.

Keep a user-provided specification unchanged. If it must change, describe the function, reason, edit, and semantic change in agent_output.md and return it to main. Continue in the same attempt after user approval and unfreeze.

## Required Reading

1. Read [the design, authoring, and repair workflow](workflows/annotation-designing.md) in full.
2. Read [the annotation design guide](docs/annotation-design-guide.md), [the QCP C annotation authoring reference](docs/annotation-authoring-reference.md), [the specification and function-contract knowledge rules](docs/spec-and-contract-knowledge.md), and [the checklist](docs/design-and-annotation-checklist.md) in full. The added knowledge rules constrain artifact contents without changing the workflow.
3. For arrays or strings, read [arrays and strings](docs/array-string-guide.md).
4. For pure propositions, finite quantification, or witnesses, read [pure proposition predicates](docs/pure-proposition-predicates.md).
5. When an ordinary Assert is needed, read [ordinary Assert placement](docs/semantic-assert-placement.md).
6. For concrete patterns, read [the concise predicate examples](docs/internal-predicate-examples.md); read only the relevant binary-answer or algorithm-mirror example when needed.

Follow the workflow's input and write boundaries, commands, retry, report, and finalize-repair contracts. Never edit the proof manual or write proofs.
