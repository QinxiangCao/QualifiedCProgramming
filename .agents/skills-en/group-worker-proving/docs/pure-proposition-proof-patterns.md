# Pure Proposition Proof Patterns

This guide is for group-worker proof work. When annotation uses `increasing`, `decreasing`, bounds, `sum`, case predicates wrapping `MaxMinLib` / `SumLib`, or CDCLLib names, keep annotation semantic and bridge to proof-friendly forms inside the group proof.

Do not push proof-facing forms back into C annotation. If a bridge lemma is missing, search the history named in proof_reuse.md by lemma/predicate name and read only matching candidates. Copy a useful complete helper closure with current-suffix renames; otherwise add and prove a current-group-suffixed helper in `group_worker_lib`.

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

Prove new or adapted forms as group-local helpers with the current helper suffix. Reused historical helpers also use the current suffix. Do not leave helpers in the official `*_proof_manual.v`, and never import historical candidate libraries directly.

## CNF and SAT predicates

For CDCLLib names (`models`, `cnf_sat`, `cnf_unsat`, `entails_clause`, `cnf_with_units`, the counters, `cdcl_view`), use the lemmas in `Rocq/cdcllib/sat_shared_lib.v` and `cdcl_shared_lib.v`. Do not restate a shared definition or copy a lemma under a case name or group suffix. For a strengthened case invariant, first get the shared predicate with `proj1` or the `_elim` in `formal_case_lib`. CDCLLib names are visible through the seed `formal_case_lib`'s `From CDCLLib Require Export`; `group_worker_lib` may add only `Coq` / `Coq.*` imports, never a `From CDCLLib Require`, so when the seed does not export the needed CDCLLib file, write an annotation/spec-gap blocker.

- point updates: `sat_function_update_eq` / `_neq`, not `unfold` plus a case split on `Z.eq_dec`;
- negation: `eval_literal_neg`, `eval_partial_literal_neg`, `literal_neg_involutive`;
- counters: `clause_counts_assign` / `clause_counts_clear`, `clause_false_counts` / `clause_counts_zero_false`, `clause_unit_other_false`;
- entailment: `entails_clause_in`, `entails_clause_mono`, `entails_clause_perm`, `entails_unit_step`, `entails_clause_units_weaken`;
- UNSAT: `entails_empty_cnf_unsat` from an entailed empty clause, `cnf_unsat_units_mono` for more assumptions, `models_cnf_with_units` to split assumptions off;
- SAT: `partial_clause_has_true` with `eval_partial_literal_total_agree`; for `cnf_sat` from a model, `rho_restrict_bounded` and `models_rho_restrict`;
- concatenations: there is no `models_app`; `unfold models` and use `Forall_app` / `Forall_cons`, and `in_app_iff` for `clause_satisfied`.

```coq
rewrite sat_function_update_neq by lia.
eapply entails_empty_cnf_unsat; eauto.   (* cnf_wf n F -> entails_clause F nil -> cnf_unsat n F *)
```

A generic fact CDCLLib lacks (for example transitivity of `entails_clause`) is one current-suffix helper stated over CDCLLib names only, recorded as a library gap in `group_worker_output.md`.

## Handoff rule

If annotation uses the right semantic predicate but a bridge lemma is missing, classify the issue as a group-worker helper task. Do not send it back to annotation.

Return to annotation only when annotation exposes the wrong semantics, the predicate arguments are insufficient, the loop invariant lacks necessary mathematical facts, or the current VC premises cannot imply the helper premises.
