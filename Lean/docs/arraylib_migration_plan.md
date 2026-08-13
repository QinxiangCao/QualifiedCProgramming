# ArrayLib Migration Plan

## Scope and order

The next migration unit is the pair:

1. `SeparationLogic/ArrayLibCore.v`
2. `SeparationLogic/ArrayLib.v`

`ArrayLibCore.v` depends on the already migrated `Mem`, `CommonAssertion`,
`StoreAux`, CompCert integer slice, and AUXLib list slice. Its imports of
`Idents`, `VMap`, Sets, and `Permutation` are unused by its declarations and
proofs, so those packages do not need to be expanded first.

One real prerequisite remains: extend `AUXLib.ListLib` with these five
source-reexported external listlib theorems before starting ArrayLibCore:

- `Zsublist_nil`
- `Zsublist_of_nil`
- `sublist_self`
- `sublist_cons1`
- `sublist_cons2`

This prerequisite is now recorded under `MIG-LIST-004`.

## Source inventory

`ArrayLibCore.v` contains:

- one outer module type, `ArrayLibCoreSig`;
- one nested `ELEMENT_STORE` interface with four data fields and six laws;
- 15 general array lemmas outside the element-store functor;
- 15 definitions inside `ArrayLib`;
- 159 lemmas inside `ArrayLib`;
- one tactic, `ArraySimplify`, with 20 ordered rewrite branches.

The 159 functor lemmas divide naturally into 48 basic/unfolding lemmas, 46
transition lemmas, 46 split/merge lemmas, and 19 alignment/range/list-tail
lemmas. The source has 233 `lia`, 151 `sep_apply`, 46 `prop_apply`, 58
`Intros`, 23 `Split`, 13 `Exists`, and 32 `ArraySimplify` call sites.

`ArrayLib.v` contains nine element-store implementations (`char`, `uchar`,
`short`, `ushort`, `int`, `uint`, `int64`, `uint64`, and pointer), with four
definitions and six proved laws each. It then instantiates the generic array
library nine times. The source total is 36 definitions and 54 lemmas, plus
the module-type and module-instantiation surface.

## Phase 0: external listlib slice

Add the five missing theorems to the existing positional/length part of
`AUXLib.ListLib`. Preserve their source names, binder order, hypotheses, and
conclusion directions. Do not add global simp attributes.

Tests must cover empty input, `hi <= lo`, full-list slicing, head-preserving
slice, tail slice, negative bounds through `Int.toNat`, and exact API types.
Run the complete `auxlibs` build before proceeding.

## Phase 1: module-functor facade prototype

Represent `ELEMENT_STORE` as a first-class Lean structure. Its six Coq
`Axiom` members become proof fields, not global Lean axioms.

Prototype the Coq functor with a small descriptor value:

```lean
structure ArrayLibInstance ... where
  elementStore : ELEMENT_STORE ...

def ArrayLib (ES : ELEMENT_STORE ...) : ArrayLibInstance ... :=
  ⟨ES⟩
```

Define generic operations and laws in namespace `ArrayLib`, taking the
descriptor as their first argument. Lean field notation should then preserve
the important source forms:

```lean
def ElemArray := ArrayLib ES
#check ElemArray.full
#check ElemArray.full_Zlength
#check CharArray.full
```

This prototype is a gate. Do not port the 174 lemmas until generic and
concrete call shapes, implicit logic parameters, and theorem rewriting have
all been demonstrated in a compile-time test. If field notation cannot keep
these forms stable, stop and compare a record API with generated namespace
aliases before selecting a facade. Record the selected unavoidable Coq-module
versus Lean-value difference in `migration_inconsistencies.md`.

`ArrayLibCoreSig` and `ArrayLibSig` should follow the existing canonical
marker-facade convention; they must retain all source parameters.

## Phase 2: general core and definitions

Create the stable facade `SimpleC.SL.ArrayLibCore`, with implementation files
split below it:

- `ArrayLibCore/General.lean`: the 15 general array lemmas;
- `ArrayLibCore/Definitions.lean`: `mixedstoreA`, segment/full/missing/shape
  variants, `repeat_Z`, and `SingleSome`;
- `ArrayLibCore/Basic.lean`: the 48 length, validity, empty, singleton, and
  unfolding lemmas.

Preserve `Int` lengths and the source `Int.toNat` behavior. In particular,
negative lengths must continue to produce empty recursive arrays where the
source does so. Keep all theorem premise order and entailment direction.

Add an exact-type API manifest and executable tests for zero, singleton,
negative, mixed `some`/`none`, missing-index, and shape assertions before
moving on.

## Phase 3: ArraySimplify

Implement a same-spelling `ArraySimplify` Lean tactic. It must retain the 20
source branch priorities and repeat until no branch makes progress. A goal
with no matching array form must remain a successful no-op.

Tests must exercise every branch separately, repeated/nested normalization,
overlapping eligible forms, arithmetic side-goal order, no-op behavior, and
the source-shaped calls used later in the file. The tactic must rewrite the
goal only, as the source `rewrite` calls do. Any difference in success,
failure, branch choice, or residual goal shape must be reported before the
transition lemmas are migrated.

## Phase 4: transition lemmas

Place the 46 transition lemmas in `ArrayLibCore/Transitions.lean`. Migrate by
families (`seg`, `mixed_seg`, `full`, `mixed_full`, `undef`, `shape`, and
`missing_i`) so each family can be API-checked and behavior-tested before the
next one is added.

Use the existing `Intros`, `Exists`, `Split`, `sep_apply`, `prop_apply`, and
`entailer!` implementations with source-shaped regression proofs. Tactic
success alone is insufficient: include representative checks of the exact
remaining assertion or closed entailment for every family.

## Phase 5: split, merge, and alignment

Put the 46 split/merge lemmas in `ArrayLibCore/SplitMerge.lean` and the final
19 lemmas in `ArrayLibCore/Alignment.lean`.

Behavior tests must cover splits at the head, middle, and tail; replacement
at the selected index; mixed initialized/uninitialized arrays; round-trip
split then merge; adjacent segment merge; shape-only resources; conversion
to alignment resources; maximum-length bounds; and `repeat_Z` at negative,
zero, and positive lengths.

## Arithmetic policy

Continue the current no-Mathlib policy. Map Presburger uses of Coq `lia` to
`omega`. For source goals that normalize expressions such as
`n * sizeA + lo * sizeA = (n + lo) * sizeA`, use explicit Lean integer
distributivity/associativity lemmas and `ac_rfl`; do not broaden `omega` or
introduce a global LIA compatibility tactic.

If a successful source proof requires a genuine nonlinear inequality that
cannot be reconstructed from existing hypotheses and core integer lemmas,
stop at that theorem and report its exact target. Do not weaken the theorem,
add an axiom, or silently introduce Mathlib.

## Phase 6: concrete ArrayLib

Migrate the nine `ELEMENT_STORE` implementations in `SimpleC.SL.ArrayLib`.
For each implementation, check:

- `A = Int` and the exact element width (`1`, `2`, `4`, or `8`);
- initialized and uninitialized address computation;
- initialized-to-uninitialized weakening;
- initialized and uninitialized shift equivalence;
- conversion to `store_align_n`;
- the strict `0 < sizeA < Int.max_unsigned` law.

Instantiate all nine array descriptors and compile source-shaped calls such as
`CharArray.full`, `IntArray.missing_i`, and `PtrArray.full_to_align`.

## Acceptance gates

- `lake build` passes for `auxlibs` after Phase 0 and for
  `SeparationLogic` after every later phase.
- Exact API manifests cover every source definition, theorem, interface field,
  and binder visibility; sorted source/Lean inventories have no omissions.
- The `ArraySimplify` suite covers all 20 branches and its observable no-op,
  repetition, and side-goal behavior.
- Axiom collection over generic ArrayLibCore permits only Lean foundations.
  Concrete ArrayLib proofs may additionally use only the already documented
  source CNotation `sizeof_*` axioms that their Coq proofs use.
- No `sorry`, `admit`, new global `axiom`, `unsafe`, source-absent global simp
  attribute, or Mathlib dependency is introduced.
- Perform an independent read-only review after ArrayLibCore and again after
  all nine concrete instances. The review must focus on tactic coverage,
  module-facade call shapes, negative-length behavior, and split/merge theorem
  directions.

After this pair is accepted, the dependency order is
`Array2LibCore -> Array2Lib`, then `PtrArray2LibCore -> PtrArray2Lib`;
`StringLib` is independently available once ArrayLib is complete. `MapLib`
depends directly on StoreAux and can be planned as a separate branch.
