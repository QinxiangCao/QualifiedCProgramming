# Annotation Design Guide

This guide covers design decisions. The workflow controls commands, write boundaries, and reports.

## 1. Specification Before Annotation

Derive a natural-language specification from the problem before writing the Rocq specification, C function contract, or loop invariant.

    Signature
      function, input types, and output type

    Preconditions
      input ranges, lengths, and relationships

    Output
      what makes an output correct

Use samples only to resolve ambiguities such as indexing, order, and branch meaning. Editorials, algorithm hints, and C control flow do not define Output.

Use a functional specification when the output is unique and state its value directly. Use a relational specification, Valid inputs out, when several outputs are accepted. Keep that choice consistent in natural-language Output, Rocq Spec, and C Ensure.

A top-level specification should also apply to another reasonable implementation. Replace current loop locals, DP transitions, scratch-table construction order, or a Fixpoint that replays the C code with the mathematical relation stated by the problem.

Quantify a problem object that is implicit but not an input directly with exists in Spec.

## 2. Rocq Form

Translate only after fixing the natural-language meaning:

- Pre inputs : Prop states input conditions;
- Spec inputs out : Prop states the output relation;
- retain a helper definition only when its name clarifies the problem.

Common forms:

| Output | Form |
|---|---|
| unique value | out = expression |
| count | out = #(fun x => P x) |
| minimum or maximum | min_value_of_subset / max_value_of_subset |
| any valid result | Valid inputs out |
| sentinel return | direct branches for sentinel and normal results |
| results of different shapes | an existing Inductive, option, or sum |
| total operation sequence | apply_op and fold |
| relational operation sequence | relation composition |

Use Z and Z-indexed list interfaces for logical integers, lengths, and indices. Use lists for ordered objects and set predicates for unordered choices. Use Forall for index-independent elementwise conditions and Forall2 for corresponding elements; retain guarded indexed quantification only for properties that depend on positions or relationships across indices.

## 3. Reuse Core Predicates First

Search in this order:

1. the dependencies fixed by the current handoff;
2. the canonical case library;
3. shared libraries;
4. mathematical predicates already defined by the current case.

Common interfaces:

| Need | Reuse |
|---|---|
| C array resources | IntArray::full, seg, undef_seg, and corresponding families |
| list length, access, slice, update | Zlength, Znth, sublist, replace_Znth |
| elementwise or pairwise relations | Forall, Forall2 |
| membership, distinctness, rearrangement | In, NoDup, Permutation |
| monotonicity | one existing increasing/decreasing or mono family |
| finite choices and counting | set predicates, #, existing Finite instances |
| sums and range enumeration | sum_range / sum / sum_set_R and Zrange, selected by signature |
| minima and maxima | min_value_of_subset and max_value_of_subset from MaxMinLib |
| graphs | valid_vpath, reachable |
| zero or more relation steps | clos_refl_trans |

Use one existing interface for each kind of property throughout a case. Do not add a second monotonicity definition for annotation convenience.

Extrema, sums, range enumeration, and reflexive-transitive closure must use these specified library semantics. Do not define IsMinimum / IsMaximum, recursive list sums, range enumeration, or a synonymous Reachable. See [knowledge rules §2](spec-and-contract-knowledge.md#2-arithmetic-and-library-interfaces) for imports, arguments, Finite instances, and endpoints.

Directly write existing expressions for:

- aliases of In, Permutation, sum, monotonicity, extrema, or reachable;
- one range, equality, or index condition;
- input-condition bundles such as InputValid, InputBound, or SizeSafe;
- predicates that only preserve temporary variables, guards, or loop control;
- an algorithm definition that simulates the current implementation.

Do not add layers around combinations of core predicates either. Write `Permutation input output /\ increasing output`, `sum (sublist lo hi l)`, or an existing maximum relation directly instead of defining forwarding names such as `SortedResult`, `RangeSumValue`, or `PrefixMaximum`.

When the final problem meaning or a cross-function interface needs a name, retain one case predicate:

    core predicate
      -> one necessary problem or interface predicate
      -> Spec / helper / invariant

Helpers, loop state, and Ensure refer directly to that layer. Do not add a second synonymous wrapper.

## 4. Conditions for a New Predicate

A new predicate must:

- express a clear mathematical property from the problem, a helper interface, or a loop;
- be less clear when written as a direct combination of core predicates;
- clearly name a problem or interface concept, or replace a substantial repeated formula;
- contain only logical parameters needed for its meaning;
- be reused by every consumer of that property.

A once-used predicate may remain when its name directly identifies a problem concept. Do not retain a wrapper around one range, equality, or existing predicate.

The final output property is the main definition. Helper contracts and Ensure refer to it directly. When a loop needs processed-state progress, that progress predicate also refers directly to the main definition:

    core result predicate -> helper contract
    core result predicate -> function Ensure
    core result predicate -> necessary progress predicate -> loop invariant

Do not expand or rename the same property separately in the specification, helper, and invariant.

Express spatial ownership separately with IntArray, string, list, or structure predicates. Result, helper, and progress pure predicates contain mathematics only, without input restrictions, capacities, or execution-safety conditions. State those conditions directly in Pre premises or the relevant C annotation, along with necessary array-read bindings and @pre bridges. Retain problem candidate sets, valid quantification domains, and answer intervals as mathematical meaning under [knowledge rules §0](spec-and-contract-knowledge.md#0-separate-mathematics-premise-ranges-and-spatial-resources).

## 5. Map to C Function Contracts

- With introduces logical values corresponding to resources;
- Require directly states input ranges, lengths, overflow conditions, and input resources;
- the mathematical part of Ensure invokes only the required final output relation, returning spatial resources separately without copying input ranges, execution-safety conditions, or intermediate construction state;
- the top-level function connects directly to the problem Spec;
- a helper exposes only the abstract result used by its caller.

Expand input sizes, scalar ranges, element ranges, and execution-safety conditions directly. Do not introduce InputValid, InputValues, InputBound, or SizeSafe wrappers.

Workspace contents enter a public helper meaning only when the caller depends on them. Otherwise Ensure returns the resource and states only the required mathematical result.

## 6. Loop Invariants

Write one sentence of mathematical progress for each loop. Keep only:

    progress
    + ranges and overflow facts needed by the next step
    + live resources
    + necessary read bindings and @pre bridges
    + an existing or necessary mathematical predicate

An invariant must initialize at loop entry, be preserved by one iteration, and imply the next phase or Ensure when the guard is false.

Do not copy every function-entry condition. Do not repeat length and interval facts already supplied by IntArray::full, seg, or another resource. State actual access bounds directly in the invariant, outside progress predicates. Use Forall over the required list or sublist for index-independent element ranges.

After v = a[i], retain the bounds, array resource, and v = Znth i l default when later reasoning needs the logical value. Split prefix, current, and suffix only when those regions have independent mathematical or spatial meaning.

Put exactly one Inv Assert before every loop. Use an ordinary Assert only for state that symbolic execution cannot determine and later verification needs. It may appear before an if, but not before a return or an Inv Assert.

## 7. Concise RMQ Example

See [the concise predicate examples](internal-predicate-examples.md#2-rmq) for the original C annotations, original Rocq definitions, line-by-line analysis, and reduced code.

RMQ needs only a few stable predicates:

- RangeMaximum: interval maximum, implemented with the existing maximum interface;
- SparseTableBuilt: the table meaning shared by build and query, referring to RangeMaximum;
- BuiltLevels: the only construction-progress predicate, covering completed levels and the current prefix while referring to RangeMaximum.

In this RMQ example, `build` performs table zeroing, base-column construction, and level-by-level construction, while `query` loops to find a power of two not exceeding the interval length. Its eight original definitions reduce as follows:

| Current definition | Treatment |
|---|---|
| Power2 | reuse the existing power operation; retain a transparent name only when annotation syntax needs it |
| RangeMaximum | retain as the only interval-maximum interface and refer directly to the existing maximum predicate |
| ZeroedPrefix | remove; write the range, safety facts, bridges, and arr/st resources directly in the zeroing loop |
| BaseColumnBuilt | merge into BuiltLevels |
| BuiltLevels | retain as the only construction progress predicate |
| LevelPrefixBuilt | merge into BuiltLevels |
| SparseTableBuilt | retain as the shared table interface for build and query |
| LogSearchState | remove; write pow = 2^k and pow <= len directly |

Do not add CellMaximum, LevelRangeMaximum, or another name that only wraps RangeMaximum. SparseTableBuilt and BuiltLevels refer directly to RangeMaximum, which refers directly to the core maximum interface.

Their relation is:

    existing maximum predicate -> RangeMaximum
    RangeMaximum -> BuiltLevels
    RangeMaximum -> SparseTableBuilt
    completed BuiltLevels -> SparseTableBuilt
    SparseTableBuilt -> build/query function contracts

Remove or inline:

- the zeroing loop does not need ZeroedPrefix; retain its idx range, n * K safety facts, necessary bridges, and arr/st resources directly;
- merge BaseColumnBuilt and LevelPrefixBuilt into BuiltLevels;
- write pow = 2^k and 2^k <= len directly in the query invariant instead of LogSearchState;
- reuse the existing power operation, retaining a transparent Power2 name only when annotation syntax needs it.

Zeroing loop:

    necessary bridges for unchanged parameters
    + 1 <= n, 1 <= K, n * K <= 1000000
    + 0 <= idx <= n * K
    + full arr and st array resources

Construction loop:

    required j / i ranges
    + next-access and arithmetic conditions
    + arr and st resources
    + BuiltLevels

Query loop:

    len = right - left + 1
    + pow = 2^k
    + pow <= len
    + required n / K / capacity, query-interval, and k / pow ranges
    + SparseTableBuilt
    + st resource

## 8. Witnesses

Choose in this order:

1. a direct value when the input uniquely determines it and the expression is clear;
2. a list for a finite ordered object;
3. a function witness only when the object is naturally a mapping.

For exists f, state its valid domain and constraints and reuse an existing construction interface. Do not default a finite sequence to a higher-order function.

## 9. Repair Boundary

Return to annotation when:

- a premise lacks a read binding, guard, overflow fact, resource, or necessary @pre bridge;
- a helper's mathematical premise is absent from the contract or invariant;
- Ensure contains only shape or ranges and no output meaning;
- loop exit does not connect to the next phase or Ensure;
- a predicate duplicates a core interface or only records control state;
- a predicate cannot initialize or be preserved.

Leave to proving:

- the mathematical predicate is exposed correctly and only a bridge lemma is missing;
- sublist, replace_Znth, Permutation, sum, extrema, or arithmetic facts require proof.
