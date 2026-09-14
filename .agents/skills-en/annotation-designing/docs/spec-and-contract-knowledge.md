# Specification and Function-Contract Knowledge Rules

This document defines knowledge requirements for the final Rocq specification and QCP function contracts. It adds no procedural requirements beyond the existing workflow, which remains authoritative for execution order and write boundaries.

The rules distinguish three layers:

- `Pre` / `Spec` and case-level helpers describe the problem's mathematics;
- `Require` / `Ensure` connect that meaning to C parameters, pre-state / post-state, and ownership;
- `Assert` / `Inv Assert` describe intermediate program points without changing the top-level input/output relation.

## 1. Types and Encodings

### 1.1 Use `Z` and Z-indexed list interfaces

Use `Z` for mathematical integers, lengths, and indices. Do not introduce `nat`, `length`, `nth`, or `nat` subtraction in a new specification or helper. Use `Zlength`, `Znth`, `sublist`, and `replace_Znth`.

### 1.2 Characters are decimal source-character codes

Represent character sequences as `list Z` and two-dimensional character grids as `list (list Z)`. Do not use `ascii`, `list ascii`, `%char`, `ascii_dec`, `nat_of_ascii`, `ascii_of_nat`, or a `CharCode` wrapper.

The input format, not the visual appearance of a character, determines its representation:

| input format | representation |
|---|---|
| a string `s` on one line | source-character codes, such as `'0' = 48` and `'1' = 49` |
| `n` integers on one line | numeric `Z`, such as `0` and `1` |

Digits in strings remain character codes. Do not privately recode `'0'` / `'1'` as `0` / `1`, or symbols such as `S` / `F` and `<` / `=` / `>` as a private alphabet. Write the real codes directly and optionally explain them in a comment, for example `S = 83`, `F = 70`, and `< = 60`; do not add aliases such as `ch_zero` or `ch_one`. Apply the same rule to character-valued outputs.

### 1.3 Numeric 0/1 data does not become `bool`

A flag, digit, matrix entry, or state supplied by the problem as an integer remains `Z`. Use `bool` only when the statement itself defines a Boolean semantic object or operation, and then use Boolean operations such as `xorb`, `negb`, and `Bool.eqb` rather than simulating them with integer addition followed by `mod 2`.

A two-way printed verdict such as `YES` / `NO` follows the statement's convention; absent another convention, use `out : Z` with `1` for positive and `0` for negative. Preserve a named sentinel such as `-1`. A result described as “a length or `-1`” remains one `Z` with a disjunction over its branches; do not introduce `bool` or an `Inductive` that merely wraps an ordinary value.

### 1.4 `Inductive` types and collection representations

Do not introduce an `Inductive` for an input alphabet, operation chain, reachability relation, or ordinary-value wrapper. Consider a minimal output-only datatype only when output alternatives carry genuinely different payload shapes and no existing sentinel, `option`, or `sum` states them clearly; prefer an existing type.

Use `list` for intrinsically ordered sequences. Represent a subset, selection, or other unordered choice as a set predicate `A -> Prop`, using `#` / `sum` for cardinality or aggregation. Do not model an unordered collection as `list Z` plus `NoDup`.

## 2. Arithmetic and Library Interfaces

### 2.1 Use `mod` only for genuine residue or wrap-around semantics

Write divisibility as `(d | n)`, non-divisibility as `~ (d | n)`, and parity as `(2 | n)` or `exists k, n = 2 * k` / `n = 2 * k + 1`. A circular-opposition condition that can be stated directly as `a + n / 2 = b \/ b + n / 2 = a` does not need `mod` either. Use `mod` only when the problem contract genuinely concerns a residue class or wrap-around and no more direct relation expresses it. Parenthesize `(d | n)` inside `/\` or `\/` chains.

### 2.2 Reuse extrema, monotonicity, quantification, sums, and reachability

- Express minima and maxima with `min_value_of_subset` / `max_value_of_subset`. Do not hand-roll `IsMinimum` / `IsMaximum` or synthesize an extremum through a classical-choice API. Include the statement's sentinel / `NO` branch when the candidate set may be empty; an extremum over an empty set by itself makes `Spec` unsatisfiable.
- Do not hand-roll all-pairs or adjacent-`Znth` monotonicity, and do not introduce stdlib `Sorted` as a synonymous interface. Use the canonical family already selected by the current dependency. Use `mono_inc` / `mono_nondec` / `mono_dec` / `mono_noninc` when that family is available; retain an annotation-facing library's established `increasing` / `decreasing` family when it is already fixed. Do not mix synonymous families within one case.
- Use `Forall` for elementwise properties independent of the index, `Forall2` for corresponding positions, `Permutation` for rearrangement, and `In` for membership. A genuinely index-dependent condition such as `p_i < i` must remain indexed and must not be weakened to a value-only `Forall`.
- Do not write a custom `Fixpoint` by default to reimplement a list sum, range enumeration, or state fold. Use `sum_range` / `sum` / `sum_set_R`, `Zrange`, `map`, and `fold_left` / `fold_right`. For partial or relational transitions, use existing one-step relations, `Rels.id`, and relation composition.
- Do not define recursive `Reachable` or a path `Inductive`. Use `valid_vpath` / `reachable` with the instance matching the vertex type, adding `NoDup` for a simple path; use `clos_refl_trans` or relation composition where appropriate.

### 2.3 Do not retain `Zrange` solely as index scaffolding

`Zrange lo hi` denotes the half-open interval `[lo, hi)`: `Zrange 0 n` is `0 .. n-1`, and `Zrange 1 (n+1)` is `1 .. n`. Do not wrap it in an identity or shift `map` when a shifted range or direct list operation states the same value:

| redundant expression | direct expression |
|---|---|
| `map (fun i => i + k) (Zrange 0 n)` | `Zrange k (n + k)` |
| `map (fun i => i) (Zrange 0 n)` | `Zrange 0 n` |
| `map (fun i => f (Znth i a 0)) (Zrange 0 (Zlength a))` | `map f a` |
| compute from the same index in `a` and `b` | `map` over `combine a b` |

Retain range enumeration only when `i` also participates in a shifted read, index arithmetic, or an index predicate.

### 2.4 Finite-set expressions must actually elaborate

Every `#P` and `sum P f` must obtain a real `Finite P` instance. Preserve predicate shapes recognized by the library and use an existing module that supplies the instance. A mathematically finite expression that Rocq cannot elaborate is not a deliverable specification.

### 2.5 A negative `Znth` index does not return the default

`Znth n l d` indexes through `Z.to_nat n`; a negative number maps to `0`, so `Znth (-1) l d` reads the first element instead of returning `d`. Judge safety from whether the enclosing precondition or quantifier admits a negative index, not merely from the presence of subtraction in the expression.

If the context can make the index negative, guard the read or tighten the quantified range. If the context already proves non-negativity, do not add a redundant guard. For example:

```coq
(* At i = 0, i - 1 is negative and incorrectly aliases the first element. *)
forall i, 0 <= i < Zlength l -> P (Znth (i - 1) l 0)

(* Guard the read. *)
forall i, 0 <= i < Zlength l ->
  P (if 0 <=? i - 1 then Znth (i - 1) l 0 else 0)

(* Or exclude the boundary value that is not needed. *)
forall i, 1 <= i < Zlength l -> P (Znth (i - 1) l 0)
```

## 3. Definition Hygiene

### 3.1 Remove names with no semantic increment

Do not retain:

- a trivial type alias such as `Definition Answer : Type := Z`;
- an alias of an existing predicate such as `Definition Occurs a x := In x a`;
- a bare range wrapper such as an `OnCircle` that only states `1 <= x <= n`;
- a helper that recomputes a value already bound by `Spec`;
- an opaque gadget such as sign multiplication in place of direct result branches;
- an identity bridge that merely renames `Pre` / `Spec` as `ReturnedResult` while preserving the same arguments in the same order.

A representation bridge is useful only when it performs actual decoding or encoding, a type or layout conversion, tag or sentinel interpretation, composite reconstruction, or pre-state / post-state selection. When removing an identity or unused bridge, also remove its transitively unused declaration, import, and mapping entry. Do not modify a frozen `Pre` or `Spec` as part of that cleanup.

### 3.2 Do not immediately apply a lambda

Do not place a lambda in head position and immediately apply it; call the target function directly. If the lambda only provides a type ascription, put the type on the definition's arguments. A lambda passed as a higher-order argument, such as the measure `fun x => x`, is fine.

```coq
(* Do not write this. *)
Definition D (x : Z) : Prop := (fun Q : Z -> Prop => Q x) P.

(* Write this directly. *)
Definition D (x : Z) : Prop := P x.
```

### 3.3 Do not force several concepts into one definition

Removing wrappers does not mean inlining everything into one giant term. Split a definition when any of the following holds:

- the same nontrivial subexpression occurs twice;
- one body mixes a validity condition with a measure;
- an inner `exists` has a witness with its own group of conditions;
- the statement already gives the concept a clear name.

For example, separate `StreetWalk ... path` from `WalkLength path`, then write `exists path, StreetWalk ... path /\ v = WalkLength path`. A concept of the form `v = expression` should be a value-producing function rather than a `Prop` that merely wraps the equality.

A helper should name a problem concept, a cross-function interface, or a repeated nontrivial formula. As a reading test, if a definition takes three sentences to explain, it usually contains three concepts.

## 4. Faithfulness to the Problem

### 4.1 Do not replace the problem with a derived characterization

Do not use a closed form, solved case split, or simplification whose equivalence first needs to be proved as the specification. Quantify over the statement's objects directly. Bind an implicit background quantity with `exists` and its defining properties rather than replacing it with a computed formula.

### 4.2 Preserve indices, order, and correspondence

- Keep an indexed bound such as `p_i < i` indexed; a value-only bound is not the same specification.
- Do not collapse a common prefix, walk, operation order, or corresponding-position constraint into unordered membership or set intersection.
- When inputs and outputs are ordered sequences, do not lose order or duplicate information merely to use a set interface.

### 4.3 Cover every output branch and preserve totality

Every branch of `output_format` must appear in `Spec`. For every input satisfying `Pre`, at least one output must satisfy `Spec`, including `-1`, `NO`, an empty output, or another exceptional branch named by the statement. When a candidate set may be empty, an extremum branch alone is insufficient.

### 4.4 `Pre` contains every single-case guarantee from the statement

`Pre` must not admit an input excluded by the problem. In addition to scalar and element ranges, retain relationships that single-value ranges cannot detect, including:

- two strings being different or having equal lengths;
- distinct points, edges, or keys;
- a guarantee that a solution exists;
- size, shape, or consistency relationships among parameters.

Test this against output totality in reverse: if a degenerate input satisfies the current `Pre` but lets `Spec` accept an output forbidden by the output format, a condition is missing. For example, omitting `s <> t` may make an empty operation sequence valid even though the statement requires `1 <= m`.

A bound on the number of test cases or a sum over all test cases constrains an outer driver rather than one solver call and need not be forced into a single-case `Pre`. Do not silently discard any other statement guarantee.

## 5. Range Visibility in `Require`

This section requires simple input ranges to be expanded in `Require`; it does not require expansion in `Ensure`. `Ensure` may call the complete `Spec` and encapsulate output ranges and post-state array conditions.

### 5.1 Give every scalar parameter an explicit range

For every simple input scalar in the C signature, especially `n`, `m`, `k`, row or column counts, and capacities, state the bounds supplied by the problem directly in `Require`. Do not rely only on an opaque `Pre` call or a spatial predicate.

None of the following substitutes for a scalar bound:

- `k == Zlength(cold_costs)` relates a scalar to a list but bounds neither one;
- an extent in `Int64Array::full(cold, k + 1, l)` describes a resource length but not the problem's range;
- derivability from other clauses does not explicitly carry the statement's guarantee. If the statement gives `1 <= k <= K`, write both sides directly.

Also state implementation-specific overflow, representability, and access-safety conditions directly in `Require`, but do not promote an implementation convenience into a problem-domain condition in `Pre`.

### 5.2 Use a guarded `forall` for a simple element domain

When the element domain of an input or input-output array or buffer can be stated clearly as an equality or interval, write an explicit indexed quantifier in `Require`:

```c
forall i,
  0 <= i && i < logical_extent =>
  lower <= Znth(i, values, 0) && Znth(i, values, 0) <= upper
```

A length equation, capacity bound, or spatial predicate such as `TArray::full` does not itself state an element range. For a two-dimensional object, guard both row and column indices and state the applicable cell range.

A condition that genuinely relates positions, several indices or arrays, prefixes, aggregate equations, or structure may remain in the complete `Pre` or an existing business predicate instead of being forced into a simple per-element interval. For example, a recurrence among `partial[i + 1]`, `partial[i]`, and `years[a - 1 + i]` is not a simple element range.

Do not add `InputValid`, `InputValues`, `InputBound`, or `SizeSafe` merely to hide simple ranges. Direct ranges and a retained complete `Pre` may coexist: the former gives the QCP contract visibility, while the latter preserves unexpanded cross-argument and structural semantics. Restating a clause in `Require` never licenses deleting or weakening the Rocq `Pre`; a user-provided `Pre` remains subject to the freeze rule.

### 5.3 A statement constraint cannot disappear merely because `Pre` omitted it

The final semantics of `Pre` and `Require` together must carry every guarantee for one invocation: scalar bounds, array lengths, element domains, and cross-argument relations. Do not infer completeness backward from an existing `Pre`; a condition never written into `Pre` cannot be recovered automatically by expanding it.

## 6. Semantic Connections in a QCP Contract

### 6.1 `Spec` reads pre-state inputs

Even when C mutates or reuses an input buffer, decode the logical input passed to `Spec` from pre-state contents. A post-state list describes an output or returned resource and must not silently replace the problem input.

### 6.2 A representation bridge does not compute the answer

A contract-level bridge handles representation only: layout, tags, sentinels, old/new state, or composite reconstruction. It does not contain a solver formula or restate how the answer is computed. This kind of representation bridge is distinct from an assertion-level value bridge such as `n == n@pre`.

### 6.3 Separate domain conditions from implementation conditions

Problem-domain conditions come from `Pre`; C contributes representability, layout, ownership, index-safety, and overflow conditions. Do not strengthen the mathematical `Pre` with an implementation-derived restriction merely to fit one implementation.

### 6.4 Connect every output to a real channel

Every output component and every branch of `Spec` must map to a real C return value or post-state memory location. An output that exists only at the logical level and has no return or post-state channel is unconnected.

## 7. Ownership of Global Objects

Every file-scope global read or written by the solver belongs to its memory footprint:

- `Require` uses a spatial predicate matching the element type, concrete layout, and actually accessed extent;
- `Ensure` returns the corresponding ownership, binding a fresh logical list when written contents are not otherwise constrained by the mathematical specification;
- use an `undef_*` entry predicate for a work array whose entry contents are irrelevant and are completely overwritten before any read; use initialized `full` when the solver relies on entry contents;
- express the extent used by the code, and retain in `Require` every explicit range needed to make that extent safe;
- a scratch global is implementation state and does not belong in the problem-level `Spec`;
- a function-local `static` has global lifetime and must also be modeled as a nameable, owned global resource.

Do not omit a write-only global. A write still requires entry ownership and returned ownership.

## 8. Two-Dimensional Logical Objects and Concrete Layouts

When a problem object is intrinsically a matrix, grid, table, board, image, or row collection, and row/column structure materially clarifies the contract, use `list (list Z)` or the corresponding nested element type. Do not flatten it merely to reuse a one-dimensional predicate.

- State the outer length, applicable row lengths, and cell ranges. Simple cell ranges in `Require` use row and column guards.
- A contiguous row-major C block uses the matching typed `Array2Lib` predicate, such as `IntArray2::full(p, rows, cols, matrix)` after confirming its signature.
- A row-pointer array such as `int **` or `char **` uses a matching `PtrArray2Lib` predicate, such as `IntPtrArray2::full(p, rows, matrix)` or `CharPtrArray2::full(p, rows, matrix)` after signature confirmation. State row lengths separately when the predicate has no column-count argument.
- Do not describe pointer-to-pointer storage as one contiguous block, or a contiguous block as independently owned rows.
- Use a two-dimensional operation such as `missing_i` only when an existing library provides the exact compatible name and signature.
- Retain a one-dimensional representation only when the object is genuinely one-dimensional or the full C interface cannot establish a sound two-dimensional shape and layout.

Do not invent a foundational two-dimensional spatial predicate. If no existing predicate matches the element type and concrete layout, do not weaken ownership with an approximation.

## 9. Predicate Availability and Signatures

Every named spatial or assertion predicate in `Require` / `Ensure` must come from an interface supported by the current repository. Its name, argument types, arity, parameter order, predicate category, and import or declaration must all be compatible. Do not introduce a new foundational memory predicate, alias, wrapper, or representation shortcut.

`forall` / `exists`, logical connectives, equality, comparison, arithmetic, and ordinary value-producing expressions are not new named predicates and may be used directly. A problem-level pure predicate remains governed by this skill's definition-hygiene rules: retain one definition in the active case library only when problem semantics or a cross-function interface needs it. Do not use it to wrap simple ranges or fabricate spatial ownership.

If existing spatial predicates and direct logical syntax cannot faithfully express the actual layout and ownership, do not approximate the contract, weaken a condition, or invent an interface with a plausible name.
