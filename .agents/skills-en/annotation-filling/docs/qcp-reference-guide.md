# QCP, References, and Resource Reclamation

This document collects annotation-round rules for symbolic execution, reference policy, and QCP resource reclamation.

## Includes and symbolic execution

C cases under `QCP_examples/LLM_bench` that reuse public `QCP_demos_LLM` headers must use bare includes consistently.

Symbolic execution must include both:

```bash
-IQCP_examples/QCP_demos_LLM/
-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM
```

`-I` supplies C header search paths; `-slp` supplies strategy/generated-Rocq logical paths. They are not interchangeable. Do not replace bare includes with long relative paths merely to invoke the tool.

## Recording checks

The annotation handoff supplies the complete `controller.py symexec` command. Controller code fixes the driver, working directory, target, and canonical `-I` / `-slp` options. On success, terminal JSON contains only the completed status. On failure, put the explicit `first_failure` category, message, location, and repair summary in `agent_output.md`; do not copy the complete argv, paths, or evidence object.

Owner symbolic execution refreshes all four generated files in the main root as one transaction: any failed step rolls back the whole set, and only success commits it. It does not run a second clean replay or create acceptance evidence. The later main-owned `clean-output-freshness/` gate replays canonical symbolic execution in an independent directory, compares the four raw generated files and manual declarations, and treats any mismatch as the controller's first failure. Stable repeated main-root digests do not replace that gate.

Only symbolic execution may refresh generated files: `*_goal.v`, `*_proof_auto.v`, `*_proof_manual.v`, and `*_goal_check.v`. Symbolic execution does not rewrite `formal_case_lib`.

## Reference policy

Prefer the reference-case hints listed in the handoff's `Problem context`. Without hints, proactively search for similar patterns in this curated scope:

- `QCP_demos_LLM`
- `QCP_examples/LLM_bench`
- `Rocq/examples/LLM_bench`

Read-only access to every reference file is allowed, including `QCP_demos_human`. Reading, searching, comparing, or noting a human example is not itself an annotation blocker. The controller's file-access policy does not encode recommendation levels and does not deny a read based on its path. At the documentation level, LLM cases remain preferred; human cases are allowed but not recommended.

A human example is only a non-authoritative source of ideas. Derive the current candidate from the current C file, `problem_context`, and `formal_case_lib`, and validate it with the current case's canonical QCP, `formal_case_lib` check, annotation-checking, later proof work, and final-check. An old report or passing status from a human case cannot replace these checks.

Do not copy ordinary read-only searches into JSON one by one. If a reference materially affected the specification design, one sentence in `agent_output.md` is enough.

`read-access denied` is not triggered by which files were read. It means the current formal candidate actually introduces a library, import, generated artifact, or other formal dependency forbidden by the phase contract. The `formal_case_lib` contract, manual-proof structure, group merge/parent verification, and final-check enforce those boundaries. A failed required check for the current case is an ordinary verification failure, not read-access denied.

Reusable patterns include read-only array scans, incrementally filled uninitialized buffers, multi-cursor array algorithms, C strings, and feasibility/optimality specifications for optimization or binary search. Do not copy long relative includes, hand edits to generated files, manual helper declarations, `Admitted.`, a new `Axiom`, or an old report's naming.

## Reference examples

Choose a similar case by data structure and proof goal:

- Ordinary annotations: `QCP_examples/QCP_demos_LLM/sum.c`, `sll.c`, `functional_queue.c`, and `majorityElement.c`.
- Refinement / safeExec annotations: `QCP_examples/QCP_demos_LLM/sll_merge_rel.c`, `kmp_rel.c`, and `int_array_merge_rel.c`.
- Branch control: `QCP_examples/QCP_demos_LLM/bubble_sort.c`, plus `QCP_examples/QCP_demos_tutorial/branch_destruct.c`, `branch_join_private_condition.c`, and `multiinv_examples.c`.
- Binary answers / feasibility predicates: `.agents/skills/annotation-filling/docs/correct-examples/split_array_largest_sum/split_array_largest_sum.c` and the sibling `binary-search-annotation.md`.

Learn the hidden properties, path naming, array-predicate choices, and mathematical specification style from these cases. Do not copy generated files, manual proof bodies, helper declarations, or old formal-file boundaries.

## Resource-reclamation errors

When QCP reports `remove permission failed` at a `return`, function end, or local-scope end, an annotation usually omitted a live local resource.

Common causes:

- A full assertion dropped a live local's `store_*(&x, v)`.
- A local array retained only its written prefix and was not recombined into a complete array before leaving scope.
- An uninitialized array was split into fragments without a complete `undef_full` or `full` before function exit.
- `by local` was incorrectly assumed to retain spatial resources.
- A raw permission was added to compensate, duplicating or mismatching an existing local store.

Diagnosis:

1. Use an independent qcp-mcp session to inspect the symbolic state immediately before the failing point.
2. If whole-function symbolic execution fails on a `return`, first check the preceding line.
3. Confirm that the state contains every live local store in the current scope.
4. For a local array, confirm that the state contains a complete array resource or that a strategy can recombine it there.

For example, before returning from a function containing `int a[2003];`, the state should normally expose `IntArray::undef_full(a, 2003)` or `IntArray::full(a, 2003, l)`, not unreclaimable prefix/suffix fragments.

Repair the missing local store or complete `full` / `undef_full`, or add the pure boundary fact needed to recombine the array segments. For reuse, record the failure point, missing resource, and final resource shape in `agent_output.md`.
