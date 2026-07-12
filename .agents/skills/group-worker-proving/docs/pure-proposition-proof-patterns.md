# Pure Proposition Proof Patterns

This guide is for group-worker proof work. When annotation uses `increasing`, `decreasing`, bounds, `sum`, or case predicates wrapping `MaxMinLib` / `SumLib`, keep annotation semantic and bridge to proof-friendly forms inside the group proof.

Do not push proof-facing forms back into C annotation. If a missing bridge lemma is needed, add and prove a current-group-suffixed helper in the group-local `case_lib`.

## Ordering predicates

Common annotation-facing forms:

```coq
increasing l
decreasing l
strict_decreasing l
```

When useful, bridge to `MonotonicList` predicates:

```coq
pose proof (proj2 (mono_nondec_iff_increasing l) Hinc) as Hmono.
unfold mono_nondec in Hmono.
specialize (Hmono i j Hi Hij Hj).
```

Common correspondences:

- `increasing l` <-> `mono_nondec l`
- `decreasing l` <-> `mono_noninc l`
- `strict_decreasing l` <-> `mono_dec l`
- strict increasing proofs usually use `mono_inc l` / `mono_inc_ind l`

Useful bridge or structure lemmas include `mono_nondec_iff_increasing`, `mono_noninc_iff_decreasing`, `mono_dec_iff_strict_decreasing`, `increasing_iff_chain`, `decreasing_iff_chain`, `strict_decreasing_iff_chain`, `mono_*_nil`, `mono_*_single`, `mono_*_cons`, `mono_*_iff_adjacent`, and `mono_*_iff_ind`.

## Bound predicates

Common annotation-facing forms:

```coq
upperbound x l
strict_upperbound x l
lowerbound x l
strict_lowerbound x l
```

Prefer existing `ListLib` intro/elimination lemmas:

- `upperbound_Znth`
- `lowerbound_Znth`
- `upperbound_intro_Znth`
- `lowerbound_intro_Znth`
- `strict_upperbound_app`
- `strict_lowerbound_cons`
- `lowerbound_app_cons`
- `lowerbound_trans`
- `lowerbound_perm`
- `upperbound_sublist_elim` / `upperbound_sublist_intro`
- `lowerbound_sublist_elim` / `lowerbound_sublist_intro`

If a VC needs a bound fact as a `Znth` inequality, eliminate the bound predicate in proof. Do not ask annotation to replace the main spec with a large `forall i` formula.

## Sum predicates

Common annotation-facing forms:

```coq
sum l
sum (sublist lo hi l)
```

First try lightweight `ListLib` lemmas such as `sum_app`, `sum_bound`, and `sum_bound_lt`.

When a proof needs range sums or finite-set sums, bridge to `SumLib` with lemmas such as `list_sum_as_Z_range_sum`, `list_sum_sublist_as_Z_range_sum`, `list_sum_map_as_Z_range_sum`, `sum_Z_range_empty`, `sum_Z_range_cons`, `sum_Z_range_split`, `sum_Z_range_le`, and `sum_Z_range_bounds`.

`ListLib.sum` is a computation over `list Z`; `SumLib.sum` is finite predicate-set summation. Bridge in proof when useful. Do not require annotation to expand a simple `sum(sublist(...))` into `SumLib.sum` merely for proof convenience.

## MaxMin predicates

Annotation should usually call a case-level predicate such as:

```coq
MinimizedMaxSegmentSum l m ans
CanSplit l m cap
CannotSplit l m cap
```

In proof, unfold those definitions and use `MaxMinLib` lemmas such as `max_unique`, `max_le`, `max_eq`, `max_union`, `max_default_*`, `min_unique`, `min_le`, `min_eq`, `min_union`, and `min_default_*`.

For binary-answer VCs, common helper shapes are:

- feasibility gives an upper bound on the optimum, for example `CanSplit l m mid -> MinimizedMaxSegmentSum l m ans -> ans <= mid`;
- infeasibility gives a lower bound on the optimum, for example `CannotSplit l m mid -> MinimizedMaxSegmentSum l m ans -> mid < ans`.

Prove these as group-local helpers with the current helper suffix. Do not leave them in the official `*_proof_manual.v`.

## Handoff rule

If annotation uses the right semantic predicate but a bridge lemma is missing, classify the issue as a group-worker helper task. Do not send it back to annotation.

Return to annotation only when annotation exposes the wrong semantics, the predicate arguments are insufficient, the loop invariant lacks necessary mathematical facts, or the current VC premises cannot imply the helper premises.
