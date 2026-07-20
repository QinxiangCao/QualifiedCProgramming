# Incorrect Example: Algorithm-Mirror Specification

This is a negative annotation example. It explains why `formal_case_lib` should not first implement a Rocq version of the C algorithm and then require the annotations to track that algorithm.

## Example files

Relevant files in this directory:

- `algorithm-mirror.md`: explains why an algorithm-mirror specification should be abandoned.
- `max_sub_array.c`: complete negative C-annotation example.
- `max_sub_array_lib.v`: negative `formal_case_lib` containing Rocq mirror definitions for a Kadane-style loop.
- `max_sub_array_goal.v`: generated VC artifact illustrating how this design pulls VCs toward algorithm-synchronization proofs. Proof/check artifacts are not retained as negative-example material.

These files are not templates. Read them to recognize bad specification and invariant shapes and to return the current case to predicate-first design early.

## Bad pattern

A common bad route is:

```coq
Fixpoint c_loop_mirror (state : LoopState) (fuel : nat) : LoopState := ...
Definition answer_spec input out :=
  out = extract_answer (c_loop_mirror (init_state input) fuel).
```

The C annotation then says:

```c
Inv Assert
  exists st,
    st == c_loop_mirror(init_state(l), i) &&
    local_x == extract_x(st) &&
    IntArray::full(a, n, l)
```

This is usually the wrong direction even when the Rocq definition itself compiles.

## Why it fails

- The specification says only how another program executes, not what mathematical property is required.
- The loop invariant hides the real prefix/suffix, bounds, and candidate answer.
- Generated VCs become fragile proofs that the C loop and Rocq mirror advance in sync.
- A small C control-flow or annotation change invalidates the mirror and its proofs transitively.

The `max_sub_array` counterexample has this form: it defines a recursive Kadane-like loop in Rocq and makes the annotations track it. A better specification defines the mathematical semantics of a maximum-subarray sum. The loop invariant directly maintains the maximum suffix of the current prefix, maximum subarray of the current prefix, bounds, and array resources.

## Replace it with predicate-first annotations

Ask which mathematical facts the current program point truly maintains:

- What are the processed prefix and unprocessed suffix?
- What form of optimality, boundary, or constraint does the current candidate represent?
- Is the array resource a whole `full`, an interval `seg`, or a shape/undefined combination?
- Which mathematical input/output relationship must hold at function exit?

Replace the mirror with predicates such as:

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

If the proof needs a connection lemma, a group worker proves it in `group_worker_lib`, or the annotation round promotes a necessary definition to the seed specification. Do not put helpers in `*_proof_manual.v`.

## Immediate rework signals

Return to annotations/specifications instead of entering vc-proving when:

- A new `Fixpoint` takes almost exactly the C loop locals as parameters.
- The invariant's central field is an executor named like `state_after_k_steps`, `run_loop`, or `simulate`.
- Only the same algorithm mirror can interpret `Ensure`; it cannot specify another implementation.
- Proof failures repeatedly demand a lockstep proof between one C step and one Rocq step.

## Lessons from `max_sub_array`

The core problem is not that a Rocq definition is syntactically forbidden; it is that the annotation direction is wrong:

- Definitions in `formal_case_lib` track C loop state instead of an independent mathematical property.
- The C invariant depends on the mirror's intermediate state and hides the prefix, suffix, optimum, bounds, and other facts that should be exposed.
- Manual VCs become proofs that C steps agree with Rocq steps rather than proofs that C satisfies a mathematical specification.

For this shape, return to the predicate-first design in `annotation-guide.md`:

- Define mathematical predicates for maximum-subarray sum, maximum suffix, and processed prefix.
- Directly maintain current-prefix optimality and array resources in the loop invariant.
- Leave pure list/max-min bridges to group-worker helpers instead of making the C annotations track a Rocq loop interpreter.
