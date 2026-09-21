# Annotation Checklist

This checklist checks artifact requirements from [the knowledge rules](spec-and-contract-knowledge.md); it adds no workflow stages or report fields.

## Specification

- Signature, Preconditions, and Output were written first.
- The specification comes only from the problem, input/output formats, and sample notes needed to remove ambiguity.
- A unique output uses a functional form; multiple accepted outputs use a relational form.
- Natural-language Output, Rocq Spec, and C Ensure are equivalent.
- The specification remains valid for another reasonable implementation.
- The top-level specification contains no current loop, DP transition, scratch-table construction, or algorithm interpreter.
- Implicit problem objects are quantified directly in Spec.
- Pre retains the problem's input guarantees. Result predicates exclude input restrictions and implementation-safety conditions while retaining legal candidates, valid quantification domains, answer intervals, and output formats.
- New specifications, helpers, and annotations use Z, Zlength, Znth, sublist, and replace_Znth for logical integers, lengths, and indices without introducing nat / length / nth representations.

## Predicates

- Current dependencies, the canonical case library, and shared libraries were searched before adding a definition.
- Existing list, Forall, Permutation, monotonicity, sum, extrema, path, and array-resource interfaces are reused.
- Extrema use min_value_of_subset / max_value_of_subset from MaxMinLib, with no custom IsMinimum / IsMaximum. Necessary case predicates directly reuse those semantics, and empty-candidate branches follow the problem.
- Sums and enumeration use sum_range / sum / sum_set_R and Zrange without recursive redefinitions. Imports, argument types, Finite instances, and closed/half-open endpoints have been checked.
- Zero or more relation steps use clos_refl_trans from the current dependencies, without a synonymous recursive Reachable / execution chain or a fixed number of compositions standing in for closure.
- Index-independent elementwise properties use Forall over the appropriate list or sublist. Corresponding elements use Forall2; genuinely position-dependent conditions retain valid index guards.
- Potentially negative Znth indices have a guard or valid domain matching the intended meaning. Negative indices are not treated as a general default mechanism; the first element of a nonempty list and the empty-list default are distinguished.
- One existing predicate family represents each kind of property throughout the case.
- There are no aliases of In, one range, one equality, or an input-condition bundle.
- Combinations of core predicates are used directly rather than placed behind successive synonymous wrappers.
- When a problem or cross-function interface needs a name, there is one case predicate and every other predicate refers to it directly.
- Every new predicate states clear mathematics, names a problem or interface concept or replaces repeated formulas, and has minimal parameters.
- The specification, helpers, and invariants refer to the same definition for the same property.
- Result, helper, and progress pure predicates and Records contain no spatial ownership, input-range bundles, or implementation-safety conditions; a different name does not hide the same range wrapper.

## Function Contracts

- Logical values in With, Require, and Ensure correspond to resources.
- Input ranges, element ranges, overflow, and execution-safety conditions are expanded directly.
- Require owns entry resources and Ensure returns them.
- The top-level function connects directly to the problem Spec.
- The mathematical part of Ensure promises only required final properties, without copying input ranges, loop-control state, safety conditions, or intermediate construction. Required resources are returned separately.
- A helper promises only the abstract result used by its caller.
- Workspace contents become a public mathematical promise only when the caller depends on them.

## Loop Invariants

- Every lexical loop has one Inv Assert.
- The plan gives one sentence of mathematical progress for every loop.
- The invariant contains only progress, next-step ranges, live resources, necessary read bindings, and @pre bridges.
- It initializes, is preserved, and connects loop exit to the next phase or Ensure.
- Function-entry conditions are not copied wholesale into every loop.
- Ranges needed downstream appear directly in annotations, outside progress predicates, following the specification's semantic boundary and the Forall rules.
- Length and interval facts supplied by array resources are not repeated.
- An @pre bridge is used only for an unchanged variable, and the current name is used afterward.
- An ordinary Assert supplies only state symbolic execution cannot determine and later verification needs.
- No ordinary Assert appears before a return or an Inv Assert.

## Plan and Retry

- function_specs gives one sentence for every C function contract.
- loop_invariants gives one sentence for every loop.
- new_predicates lists only predicates added by this case and explains why core interfaces are insufficient.
- The plan does not copy complete invariants, resources, or case-library definitions.
- The initial attempt keeps vc_comparisons empty.
- A retry compares proposition text in the old and current manuals directly.
- Each item records only the VC, annotation location, old gap, change, and result.
- Continue the current attempt while a result is unresolved; set ready only after all are resolved.

## Completion

- formal-case-lib-design passes.
- symexec passes.
- The active formal_case_lib check passes.
- Only symexec updates generated files.
- The proof manual was not edited and no proof was written in the annotation attempt.
- A successful agent_report.json contains only status: completed.
