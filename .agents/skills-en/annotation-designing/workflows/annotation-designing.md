# Annotation Design, Authoring, and Repair

One annotation owner handles the whole run:

    read the handoff, problem, and current files
      -> write a natural-language specification
      -> write the Rocq specification and C function contract
      -> reuse core predicates and write minimal loop invariants
      -> formal-case-lib-design
      -> symexec
      -> repair the first failure
      -> formal-case-lib
      -> completed

Agent-written function contracts, necessary predicates, C body annotations, case-library definitions or lemmas, and annotation_plan.json remain jointly editable in the current attempt. A user-provided specification changes only after user approval and unfreeze.

## 1. Inputs and Write Boundary

On the initial attempt, read:

- the current agent_input.md;
- problem context;
- target C file;
- canonical formal_case_lib;
- current generated manual;
- annotation_plan.json.

On retry, also read each failed VC's source attempt, name and parent, annotation location, sealed manual, and old gap, together with the original blocker files listed by the handoff.

Write only:

- function contracts, Inv Assert, and necessary ordinary Assert annotations in the target C file;
- the canonical formal_case_lib when its policy is present or create;
- the current attempt's annotation_plan.json, agent_output.md, and agent_report.json;
- generated files refreshed together by the handed-off symexec command.

Do not change ordinary C code, the proof manual, controller state, group files, shared libraries, or another case. Do not write proofs or add Admitted, axioms, or disabled lemmas. Under an absent formal_case_lib policy, keep the candidate path absent.

## 2. Derive the Specification from the Problem

Use the problem statement, input format, output format, and sample notes needed to remove ambiguity. Use the C implementation only to identify parameters, resources, and helper call relationships. Editorials and algorithm hints do not define the specification.

Write this first:

    Signature
      function name, parameter types, and return type for one case

    Preconditions
      input ranges, lengths, and relationships

    Output
      the complete mathematical relation between inputs and a correct output

For a unique output, define the value directly. When several answers are allowed, define Valid inputs out. For a sequence of operations, define one-step behavior and the final state after all steps. Multiple test cases do not enter the core specification for one case.

Then write an equivalent Rocq form:

- Pre inputs : Prop for input conditions;
- Spec inputs out : Prop for the output relation;
- a small helper definition only when its name materially clarifies the problem.

The top-level specification states what result is correct. Algorithmic classifications, derived formulas, loop variables, DP transitions, scratch tables, and data-structure construction do not enter it. Quantify a problem object that is implicit but not an input directly with exists in Spec.

Common shapes:

- closed value: out = expression;
- count: out = #(fun x => P x);
- minimum or maximum: reuse min_value_of_subset or max_value_of_subset;
- any valid answer: Valid inputs out;
- sentinel in the same return type: direct branches;
- results of different shapes: an existing Inductive, option, or sum;
- total one-step operation: apply_op and fold;
- relational one-step operation: relation composition.

Use Z for numbers. Use lists for ordered objects and set predicates for unordered choices. Prefer Forall for elementwise conditions; use Znth or Forall2 when position or correspondence matters.

Finally map the Rocq specification to C:

- With introduces logical values corresponding to resources;
- Require directly states input ranges, lengths, overflow conditions, and input resources;
- Ensure invokes the mathematical result predicate and returns resources;
- a helper promises only the abstract result used by its caller.

Natural-language Output, Rocq Spec, and C Ensure must be equivalent.

## 3. Reuse Predicates

Before writing a definition, search the current dependency set, canonical case library, and shared libraries. Prefer:

- array resources: IntArray::full, seg, undef_seg, and the corresponding families;
- lists: Zlength, Znth, sublist, replace_Znth;
- elementwise and pairwise relations: Forall, Forall2;
- membership, distinctness, and rearrangement: In, NoDup, Permutation;
- monotonicity: one existing increasing/decreasing or mono family throughout the case;
- counting, sums, and extrema: #, sum, SumLib, min_value_of_subset, max_value_of_subset;
- graphs: valid_vpath and reachable.

Use existing expressions directly for:

- aliases such as Occurs := In;
- predicates wrapping only one range or equality;
- input-condition bundles such as InputValid or SizeSafe;
- redefinitions of permutation, monotonicity, sums, extrema, or reachability;
- predicates that only record temporary variables and loop control;
- a Fixpoint or state transition that replays the current C steps.

Use combinations of core predicates directly as well. Do not add a wrapper that only forwards `Permutation input output /\ increasing output`, `sum (sublist lo hi l)`, or an existing maximum relation. When the problem output or a cross-function interface needs one name, retain one case predicate and make helpers and loops refer to it directly.

Keep a new predicate only when it:

- expresses a clear mathematical property from the problem, a helper interface, or a loop;
- cannot be stated clearly by directly combining core predicates;
- clearly names a problem or interface concept, or replaces a repeated formula;
- has only the logical parameters needed for its meaning;
- is reused by the specification, helper, or invariant wherever the property occurs.

A once-used predicate may remain when its name directly identifies a problem concept. Do not retain a wrapper around one range, equality, or existing predicate.

Use existing array, string, list, or structure predicates for spatial ownership. Pure predicates describe mathematics only.

## 4. Function Contracts and Loop Invariants

Write With, Require, and Ensure from the top-level function toward helpers. Connect the top level directly to the problem Spec. A helper's Ensure exposes only the result consumed by its caller.

Write one sentence of mathematical progress for each loop, then write its Inv Assert:

    current progress
    + ranges needed by the next access or operation
    + live resources
    + necessary @pre bridges
    + one existing or necessary mathematical predicate

Do not copy all function-entry conditions into every invariant. IntArray::full and seg already provide their own length and interval facts; do not repeat those facts. Still state the actual index bounds needed by an array access.

Use n == n@pre only when n has not changed since entry. After writing the bridge, use current n for every range, resource, and mathematical fact in the same assertion.

Each loop has one Inv Assert immediately before it. Use an ordinary Assert only for state that symbolic execution cannot determine and downstream verification needs. It may appear before an if, but not before a return or an Inv Assert.

## 5. annotation_plan.json

The plan does not duplicate C annotations or the case library. It stores short summaries:

    {
      "version": 2,
      "status": "ready",
      "function_specs": [
        {"name": "query", "meaning": "returns the maximum value in the input interval"}
      ],
      "loop_invariants": [
        {"location": "query: power loop", "progress": "pow is the current power of two not exceeding the interval length"}
      ],
      "new_predicates": [
        {
          "name": "SparseTableBuilt",
          "meaning": "each valid table cell is the maximum of its interval",
          "why_needed": "build and query share this table meaning"
        }
      ],
      "vc_comparisons": []
    }

function_specs contains one sentence for every C function contract. loop_invariants contains one sentence for every lexical loop. new_predicates contains only predicates added by this case and stays empty when shared interfaces suffice.

## 6. Checks and Retry

After each coherent edit, run the handed-off commands in order:

1. coq-check --target-kind formal-case-lib-design;
2. symexec;
3. coq-check --target-kind formal-case-lib when the policy is present or create.

Repair the specification, invariant, resource, or lemma corresponding to the first failed VC, then rerun. Only symexec updates generated files.

The initial attempt keeps vc_comparisons empty. On retry, record this for every failed VC:

    {
      "source": {
        "attempt": "<source attempt>",
        "name": "<old VC>",
        "annotation_location": "<C annotation point>"
      },
      "current": ["<current VC>"],
      "old_gap": "<missing fact or resource>",
      "change": "<specification, invariant, resource, or lemma change>",
      "result": "resolved"
    }

Read the sealed old manual and current manual directly. Compare the propositions' conclusions, pure premises, spatial resources, existentials, and witnesses. When a VC is renamed or split, current lists every VC that carries the old responsibility. A missing old name alone does not resolve the gap.

Keep editing in the current attempt while a result is unresolved. Set the plan to ready only after every failed VC is resolved.

## 7. Output and Stop

Keep agent_output.md to a short summary of this iteration's changes and VC comparisons. A successful agent_report.json is exactly:

    {"status": "completed"}

A proposal to change a user-provided specification goes only in agent_output.md and is not a terminal report. Tool blockers and structured blockers use the fields supplied by the handoff.

After writing the terminal report, stop editing and ask main to run the original finalize_invocation. If it returns report-repair-required, repair it under the same owner and attempt and rerun that invocation. Do not self-accept, prove, merge, apply, or run final-check.
