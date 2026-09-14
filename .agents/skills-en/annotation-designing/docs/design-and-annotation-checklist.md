# Annotation Checklist

## Specification

- Signature, Preconditions, and Output were written first.
- The specification comes only from the problem, input/output formats, and sample notes needed to remove ambiguity.
- A unique output uses a functional form; multiple accepted outputs use a relational form.
- Natural-language Output, Rocq Spec, and C Ensure are equivalent.
- The specification remains valid for another reasonable implementation.
- The top-level specification contains no current loop, DP transition, scratch-table construction, or algorithm interpreter.
- Implicit problem objects are quantified directly in Spec.

## Predicates

- Current dependencies, the canonical case library, and shared libraries were searched before adding a definition.
- Existing list, Forall, Permutation, monotonicity, sum, extrema, path, and array-resource interfaces are reused.
- One existing predicate family represents each kind of property throughout the case.
- There are no aliases of In, one range, one equality, or an input-condition bundle.
- Combinations of core predicates are used directly rather than placed behind successive synonymous wrappers.
- When a problem or cross-function interface needs a name, there is one case predicate and every other predicate refers to it directly.
- Every new predicate states clear mathematics, names a problem or interface concept or replaces repeated formulas, and has minimal parameters.
- The specification, helpers, and invariants refer to the same definition for the same property.
- Pure predicates do not copy spatial ownership.

## Function Contracts

- Logical values in With, Require, and Ensure correspond to resources.
- Input ranges, element ranges, overflow, and execution-safety conditions are expanded directly.
- Require owns entry resources and Ensure returns them.
- The top-level function connects directly to the problem Spec.
- A helper promises only the abstract result used by its caller.
- Workspace contents become a public mathematical promise only when the caller depends on them.

## Loop Invariants

- Every lexical loop has one Inv Assert.
- The plan gives one sentence of mathematical progress for every loop.
- The invariant contains only progress, next-step ranges, live resources, necessary read bindings, and @pre bridges.
- It initializes, is preserved, and connects loop exit to the next phase or Ensure.
- Function-entry conditions are not copied wholesale into every loop.
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
