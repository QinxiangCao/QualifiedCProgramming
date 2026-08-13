# SeparationLogic next migration plan

## Scope audit

The root Coq `Makefile` lists the following still-unmigrated files in its active
`SL_FILES` target:

1. `SeparationLogic/SeparationLogic.v`
2. `SeparationLogic/NestedCriticalSTS.v`
3. `SeparationLogic/pocv02.v`

The checkout also contains `ConAssertion_D.v`, `highlevelmonad.v`, `poc.v`, and
`pocv01.v`, but none of them belongs to the active `SL_FILES` target and no
active ANC file imports them. They are therefore legacy or experimental files,
not hidden prerequisites of the three stages below. They must not be counted as
migrated, but they should not delay the active SeparationLogic closure.

Current status: Stages 1 and 2 are complete. Stage 3 (`pocv02.v`) is deferred by
explicit user decision and has not been started.

## Stage 1: aggregate `SeparationLogic.v` (complete)

This aggregate has the highest fan-out: the C semantics and most generated
strategy goals import `SimpleC.SL.SeparationLogic`.

### Public aggregate

- Add `SimpleC/SL/SeparationLogic.lean` with namespace
  `SimpleC.SL.SeparationLogic`.
- Reconstruct `CRules` from the already migrated canonical components:
  `Assertion.SL`, `DerivedPredSig`, `StoreLibSig`, `ArrayLibSig`,
  `Array2LibSig`, `PtrArray2LibSig`, `MapLibSig`, and `StringLibSig`.
- Reconstruct `naive_C_Rules` from `ConAssertion.STS_naive`, its canonical
  `CSL`, and the same derived library stack.
- Flatten the complete included surface, not merely the names already observed
  in Cdef. Freeze the aggregate with a generated `#check` inventory and a type
  hash over every exported declaration.
- Preserve `field_address : Int -> String -> String -> Int` as the direct Lean
  counterpart of the source `Parameter`. It may appear in proof-foundation
  reports, but no source-absent assumption may be introduced.
- Preserve `should_be_equal {A} (x y : A) : Prop := True` transparently.

### Abstract StringLib members

`StringLibSig` contains two parameters and five laws. The source `CRules` and
`naive_C_Rules` materialize those assumptions through `Include StringLibSig`.
The Lean aggregate must reuse the existing `StringLibSig` structure and expose
the same seven assumptions exactly once per aggregate. It must not invent a
second, unrelated global-string theory or silently choose a concrete semantics.
The resulting representation and any extra facade-selection syntax must be
recorded in `migration_inconsistencies.md`.

### Tests

- Check every aggregate component is definitionally the intended canonical
  value and cannot carry alternative non-source semantics.
- Exercise the downstream forms used by `Cdef/AsrtDenote.v`,
  `Cdef/CStmtSem.v`, and `Cdef/CExprValHelper.v`, including byte-vector helpers,
  all scalar store/undef-store names, and direct unfolding of `mstore`.
- Exercise both abstract global-string predicates and all five laws through the
  aggregate rather than through `StringLibSig` alone.
- Check `field_address` and `should_be_equal`, and inspect their axioms.
- Run the full three-package build and reject `sorry`, `admit`, source-absent
  `axiom`, `unsafe`, and new global simp attributes.

## Stage 2: `NestedCriticalSTS.v` (complete)

This stage depends only on already migrated modules and is technically
independent of Stage 1. It is scheduled second because Stage 1 has much greater
downstream fan-out.

- Migrate `nested_critical_state` with `handlers_of_NCS : List Int` and the
  state field tied explicitly to its `critical_STS` value.
- Migrate both indexed constructors of `nested_critical_transition`, including
  the exact `Nat` length threshold and singleton-token union.
- Migrate `nested_critical_STS_to_STS`, `nested_critical_STS_def`,
  `nested_critical_STS_to_STS_def`, fixed `RTrans`/`GTrans`, and
  `NestedCriticalCSL.Critical`.
- Use data-free canonical facades for the two Coq module types, following
  `CriticalSTS.lean`; do not permit alternative implementations of fixed
  source definitions.
- Preserve the exact Coq parse of `Critical`:
  `hs = [] && (EX s', ... || (hs <> [] && ...))`. This is not the visually
  suggested two-top-level-branch form. The likely source-parenthesization risk
  and its effect on nonempty handler lists are recorded as `MIG-NESTED-R001`.

Tests must cover successful and rejected enter/exit transitions, token depth,
owned-token thresholds, R/G transparency, both assertion branches, typeclass
inference, and the concrete nested/triple-critical state shapes found in ANC.

## Stage 3: active `pocv02.v` (deferred)

This is a separate large migration, not a small tail of Stage 2. The source has
about 4,700 lines and 314 top-level declarations. Split the Lean implementation
internally while preserving the public `SimpleC.SL.pocv02` entry point:

1. `PocV02/DependentList`: indexed lists, maps, casts, and equality laws.
2. `PocV02/Environment`: type, term, function, predicate, proposition, and
   string mappings plus update laws.
3. `PocV02/Syntax`: typed expressions, assertion terms, quantified terms, and
   operations.
4. `PocV02/Denotation`: expression/assertion denotation and quantified
   semantics over `SeparationLogic.CRules`.
5. `PocV02/EqualityFreeVars`: Boolean equality, decisions, free-variable
   checks, and variable-list invariants.
6. `PocV02/Ramification`: operation execution, ramification/side conditions,
   list algebra, and denotational preservation.
7. `PocV02/Instantiation`: expression and assertion instantiation plus its
   soundness results.

Dependent transports must use Lean indexed elimination and proof irrelevance,
not unchecked casts. Coq `sumbool` results map to `Decidable`; `lia` is tried as
`omega` under the existing arithmetic policy, stopping at the first genuine
capability gap.

### Source proof hole

The active source declaration `pocv02.soundness` ends with `Admitted`; the long
attempted proof is commented out and refers to unfinished helper material. The
Lean migration must not use `sorry`, `admit`, or an axiom to reproduce this
hole. Before claiming Stage 3 complete, do one of the following explicitly:

1. prove the original statement in Lean without strengthening its premises;
2. obtain a completed Coq proof/source correction and migrate that proof; or
3. exclude the theorem and mark active `pocv02` parity blocked.

All declarations before the hole can be migrated and tested independently, but
that partial result must not be reported as complete `pocv02.v` parity.

## Acceptance order

Stages 1 and 2 have their own API inventories, behavior/source-shape tests,
`#print axioms` audits, and forbidden-placeholder scans, and both are included
in the 143-job default build. Do not start Stage 3 merely because these stages
build; first report the admitted-source decision and agree on its treatment.
