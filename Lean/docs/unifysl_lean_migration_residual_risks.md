# Unifysl Lean Migration Residual Risks

This document collects known residual risks and intentional Lean/Coq shape
differences found during the staged migration toward `demo932/Interface.v`.

## Current Validation Baseline

- `lake build Unifysl` passes in `unifysl`.
- The Lean source tree under `Unifysl` and `lakefile.lean` is clean against the
  migration-gap marker scan used during validation.
- L0-L7 public declarations are intended to follow the corresponding active
  Coq declarations. Commented legacy Coq blocks are intentionally omitted.

## Residual Risks

### Kripke Relation Typeclass Synthesis

Lean does not automatically synthesize derived `Relation` instances for
compound world types in the same way Coq instance search can appear to after
scope and instance resolution.

Affected examples:

- `Relation (A × B)` using `RelProd`
- `Relation (A -> B)` using `pointwise_relation`
- `Relation (Option A)` using `option00_relation`
- equality-backed `Relation worlds`

Current state:

- The corresponding branch-join and identity instances exist.
- They are usable when the intended `Relation` is explicit or locally supplied.

Risk:

- Downstream modules may fail to infer a compound Kripke relation automatically.

Guidance:

- Do not add broad global derived `Relation` instances casually; several
  compound types have multiple plausible relations.
- If downstream code depends on automatic synthesis, record the exact missing
  instance and decide whether to add a controlled local instance or a dedicated
  helper in the dependency module.

### Lean-Safe Notation Replacements

Some Coq ASCII notations are not Lean-safe.

Current replacements:

- Coq `x --> y` is represented as Lean `x ⟶ y`.
- Coq `x <--> y` is represented as Lean `x ⟷ y`.
- Kripke scoped `m <= n` is represented explicitly as `Krelation m n`.

Risk:

- Future ports may accidentally try to reuse Coq ASCII notation, especially
  `-->`, which Lean parses as a comment.

Guidance:

- Keep the underlying field names (`impp`, `iffp`, `Krelation`) stable.
- Prefer explicit names in complex theorem statements when notation creates
  parser or precedence ambiguity.

### Proof-Only Classes Migrated to `Prop`

Several Coq classes declared in `Type` are proof-only in practice and were
migrated as Lean `Prop` classes, following the existing Lean proof-theory style.

Risk:

- If a downstream module treats a class dictionary as computational data rather
  than proof evidence, the Lean `Prop` encoding may be too restrictive.

Guidance:

- Before changing such a class back to `Type`, check all existing instances and
  theorem statements for proof irrelevance assumptions.
- Prefer keeping proof-only algebraic laws in `Prop` unless a concrete
  downstream use requires data-carrying dictionaries.

### Shallow Quantifier Universe Polymorphism

Coq fields:

- `exp {A : Type} : (A -> expr) -> expr`
- `allp {A : Type} : (A -> expr) -> expr`

Lean fields are universe-polymorphic:

- `exp.{u,v} {A : Type v} : (A -> expr) -> expr`
- `allp.{u,v} {A : Type v} : (A -> expr) -> expr`

Risk:

- Future concrete instances may accidentally specialize to one universe and fail
  for polymorphic quantifier use.

Guidance:

- Keep future `ShallowExistsLanguage` and `ShallowForallLanguage` instances
  universe-polymorphic unless a downstream module proves that monomorphic use is
  sufficient.

### Coq Rewrite Automation vs Lean Proper Infrastructure

Coq `Proper`, `RewriteRelation`, and relation-class automation do not map
one-to-one to Lean rewrite automation.

Current state:

- Local replacements exist for relation, inclusion, same relation, `Proper`,
  `RewriteRelation`, `flipRel`, and `implRel`.
- Core theorem statements and instances are preserved where migrated.
- The downstream `SimpleC.SL.UnifyslBridge` module connects these instances to
  `AUXLib.SetoidRewrite`. It supports directional `implRel` transport,
  multi-argument partial application, and flipped input relations without
  introducing a reverse global typeclass adapter.

Risk:

- A downstream module that does not import the bridge cannot expect Coq
  `rewrite` behavior from Lean core `rw`.
- Unifysl `Reflexive` is currently a proposition-valued definition rather than
  a Lean class. New rewrite relations used as unchanged leading arguments may
  therefore need a focused `AUXLib.Reflexive` adapter in the bridge.
- `RewriteClass.v` contains anonymous Coq smoke-test goals. Lean preserves the
  exercised behavior through named smoke theorems, but the anonymous goals are
  not represented one-for-one as tests.

Guidance:

- Preserve the migrated instance names and relation directions exactly.
- Import `SimpleC.SL.UnifyslBridge` in downstream integration modules and use
  `rel_rw`; do not add a reverse AUXLib-to-unifysl `Proper` instance.
- Add a focused `AUXLib.Reflexive` bridge only when a new unifysl rewrite
  relation is actually used as an unchanged leading argument.
- If exact smoke-test parity becomes important, add a small dedicated Lean test
  file that mirrors each Coq anonymous goal explicitly.

### Ltac and Lean Tactic Coverage

Current migrated tactic surface:

- `register_typeclass` core primitives are implemented through Lean
  metaprogramming.
- `solve_assum` is implemented as a Lean tactic macro.
- `ExtensionTactic` Add* wrappers and registration primitives are implemented
  as Lean tactics.

Known remaining area:

- Later proof-theory modules may introduce additional Coq tactic wrappers
  outside the L0-L7 scope.

Risk:

- Later modules may depend on tactic behavior rather than only theorem names.
- Lean tactic syntax is not itself a term-level declaration. `ExtensionTactic`
  provides term markers such as `AddSequentCalculus : Unit` for discoverability
  and smoke checks, while the executable behavior is supplied by tactic
  elaborators of the same printed names.

Guidance:

- When such a module is migrated, port the owning tactic behavior there.
- Do not replace tactic-dependent proof obligations with weaker theorem
  statements.
- To check the term marker, prefer a type-ascribed smoke check such as
  `#check (Unifysl.AddSequentCalculus : Unit)` if bare name elaboration is
  ambiguous in a context that also imports the tactic syntax.

### Namespace Extension for `Semantics`

Lean permits extending the existing `Semantics` namespace even though
`Semantics` is also a class name.

Current extensions:

- `Semantics.impp`
- `Semantics.Kripke.impp`
- `Semantics.KripkeMono.impp`
- `Semantics.andp`
- `Semantics.orp`
- `Semantics.falsep`
- `Semantics.truep`
- `Semantics.iffp`
- `Semantics.negp`

Risk:

- Name lookup may be confusing where syntax-level connectives such as
  `Unifysl.andp` and semantic-level functions such as `Unifysl.Semantics.andp`
  are both in scope.
- The Coq Kripke minimum semantics file also used module-qualified names
  `Semantics.impp`, `SemanticsMono.impp`, and `sat_impp`. Lean cannot expose
  these at the same root names because the trivial semantics already owns
  `Semantics.impp` and root `sat_impp`.

Guidance:

- Use the qualified `Semantics.*` form for semantic connectives in statements
  and instance fields.
- Use syntax-level exported names (`andp`, `orp`, `impp`, `iffp`) only for
  expressions.
- Use `Semantics.Kripke.impp`, `Semantics.KripkeMono.impp`, and
  `KripkeMinimumSemantics.sat_impp` for Kripke minimum semantics.

### L6 Namespaced Proof Patterns and Kripke Propositional Semantics

L6 adds modules whose Coq names are commonly used through module-qualified
paths.

Current Lean shape:

- `MinimumLogic/ProofTheory/ProofTheoryPatternsP.v` is migrated under
  `Unifysl.ProofTheoryPatternsP`.
- Kripke propositional semantic connectives are under
  `Semantics.KripkePropositional`.
- Kripke propositional Mono variants are under
  `Semantics.KripkePropositionalMono`.
- Kripke propositional `sat_*` lemmas are under
  `KripkePropositionalSemantics`.

Risk:

- Downstream ports may initially look for unqualified root names such as
  `Adjointness` or `sat_andp`, but those roots are already occupied by earlier
  D1 or trivial-semantics declarations.

Guidance:

- Use qualified L6 names when referring to provable-level proof patterns or
  Kripke propositional semantic lemmas.
- Do not re-export these names to root unless a downstream module proves that
  the ambiguity can be resolved without changing existing APIs.

### L6 Semantic Equivalence as Instances

Coq states `eqR_KripkeIntuitionistic` and `Trivial2Kripke` as lemmas whose
goals build typeclass dictionaries. Lean represents these same declarations as
named instances.

Risk:

- Downstream code that expects to `apply` the Coq lemma name directly may need
  explicit instance use or a type ascription in Lean.

Guidance:

- Prefer instance search for these dictionaries.
- If a later proof genuinely needs theorem-style application syntax, add a
  small wrapper in the owning semantic-equivalence module rather than changing
  the instance declarations.

### L7 ProofTheoryPatterns Alias Module

Coq `MinimumLogic/ProofTheory/ProofTheoryPatterns.v` is an alias module:
`D1 := ProofTheoryPatternsD1` and `P := ProofTheoryPatternsP`.

Current Lean shape:

- `Unifysl.ProofTheoryPatterns.D1` exports the already-root D1 proof-pattern
  names.
- `Unifysl.ProofTheoryPatterns.P` exports the provable-level names from
  `Unifysl.ProofTheoryPatternsP`.

Risk:

- The printed type of `#check Unifysl.ProofTheoryPatterns.D1.Adjointness` may
  show the root declaration `Unifysl.Adjointness`, because Lean `export`
  creates aliases to existing constants.

Guidance:

- Use `Unifysl.ProofTheoryPatterns.D1.*` and
  `Unifysl.ProofTheoryPatterns.P.*` for module-alias style downstream ports.
- Do not additionally re-export `P` names to root; root is already occupied by
  the D1 layer.

### Separation Algebra Generator Instance Shape

`OSAGenerators` builds separation algebras for trivial, unit, identity,
option, function, sum, and product worlds.

Current state:

- Active Coq declarations are migrated.
- Coq comment-block examples such as heap, stack, and step-index helpers are
  intentionally omitted.
- Lean proofs often install local `Relation`, `Join`, or `Unit` instances
  explicitly before constructing records.

Risk:

- Downstream code may expect Coq instance search to infer generated compound
  algebras more aggressively than Lean does.
- A later module may depend on an omitted comment-block example as if it were
  part of the active API.

Guidance:

- When using generated compound algebras downstream, prefer explicit local
  `letI` bindings for the intended relation/join/unit instances.
- If a downstream file imports an omitted example, migrate that example in its
  owning layer instead of weakening the downstream theorem.

### L8 Intuitionistic Proof-Theory Registration

`PropositionalLogic/ProofTheory/Intuitionistic.v` extends the proof-theory
automation registration tables introduced by `ExtensionTactic`.

Current Lean shape:

- The L8 conversion theorems and proposition rules are root declarations under
  `Unifysl.*`.
- The new register instances live in the L8 module rather than in
  `ExtensionTactic`, so the Add* tactics discover them only after importing
  `Unifysl.PropositionalLogic.ProofTheory.Intuitionistic` or root
  `Unifysl`.
- Coq `<-->` and `-->` follow the existing Lean-safe notation choices
  `⟷` and `⟶`.

Risk:

- A downstream file importing only `ExtensionTactic` will see the base Add*
  tactic behavior but not the propositional L8 conversion registrations.
- Lean tactic elaboration and typeclass search are stricter about local
  instances than Coq Ltac plus typeclass search; proofs may need the L8 module
  imported explicitly before invoking Add*.
- `AddSequentCalculus` introduces a local `Derivable` instance and registers
  propositional sequent-calculus dictionaries against that local instance.
  Downstream smoke checks should first bind `GammaD : Derivable L :=
  inferInstance` and then synthesize `AndSequentCalculus L GammaD`, etc.;
  asking directly for the definition `Provable2Derivable` can miss
  the local-instance key.

Guidance:

- Import the L8 module before expecting Add* to synthesize propositional
  sequent calculus, axiomatization, deduction, or equivalence dictionaries.
- Keep future proposition proof-theory registrations in the file that owns the
  corresponding theorem, matching the current L8 pattern.

### L9-L10 Propositional Rewrite and Pattern Namespaces

`PropositionalLogic/ProofTheory/RewriteClass.v` and
`ProofTheoryPatterns.v` extend the minimum-logic rewrite/pattern
infrastructure with propositional connectives.

Current Lean shape:

- L9 `RewriteClass` instances use the existing Lean `Proper`,
  `RewriteRelation`, `flipRel`, and `implRel` classes rather than Coq
  `Morphisms` automation.
- L10 provable-level pattern lemmas live under
  `Unifysl.PropositionalLogic.ProofTheoryPatterns.P`.
- L10 derivable1-level pattern lemmas live under
  `Unifysl.PropositionalLogic.ProofTheoryPatterns.D1`.
- Root derived propositional rules such as `andp_orp_distr_l` and
  `iter_andp_multi_imp` remain root `Unifysl.*` declarations.

Risk:

- Downstream ports may initially look for Coq-style module aliases from
  `Require Export`. Lean uses explicit namespaces and `export`, so printed
  names may show the underlying minimum-logic constants for re-exported
  classes.
- Coq rewrite automation may solve some pattern rewrites automatically; Lean
  proofs should usually call the named proper instances or pattern lemmas
  explicitly.

Guidance:

- Use qualified `PropositionalLogic.ProofTheoryPatterns.P.*` and `.D1.*`
  names for theorem-level pattern lemmas.
- Keep root names for concrete propositional derived rules.
- Do not introduce broad new rewrite automation in downstream modules unless a
  specific proof needs it; prefer focused named lemmas.

### L11 Classical Laws and Iterated Connectives

`PropositionalLogic/ProofTheory/TheoryOfClassicalAxioms.v` and
`TheoryOfIteratedConnectives.v` are now represented by Lean modules with the
same public class, field, theorem, and constructor names where Lean syntax
allows it.

Current Lean shape:

- Classical-law classes such as `PeirceLaw`, `ByContradiction`,
  `DoubleNegElimination`, `ClassicAnalysis`, `ExcludedMiddle`, and
  `ImplyToOr` stay at root `Unifysl.*`.
- The proof chain between these classes is theorem based, matching the Coq
  declarations while relying on already migrated propositional sequent and
  provable rules.
- Iterated conjunction definitions use Lean `List.foldl` and `List.foldr`.
- `AddConnective_iter_andp` is implemented as a Lean meta tactic that verifies
  the fold-left iterated conjunction language, definition, and derived
  iterated-conjunction proof class can be synthesized.
- The L8/L11 iterated-conjunction classes mark the hidden iterated-language
  dictionary as `semiOutParam`, and L11 provides low-priority fold-left wrapper
  instances for `IterAndLanguage`, `IterAndDefinition_left`, and
  `IterAndAxiomatization_left`.

Risk:

- The earlier dependency-interface ambiguity between L8
  `IterAndAxiomatization_left` and L11 `IterAndDefinition_left` has been fixed
  by using `semiOutParam` and fold-left wrapper instances. An underspecified
  target such as `IterAndDefinition_left L` now synthesizes in the standard
  fold-left case.
- If downstream code intentionally uses a non-default opaque local
  `IterAndLanguage L` hypothesis, it should also provide the matching
  `IterAndDefinition_left` and `IterAndAxiomatization_left` instances for that
  dictionary. Otherwise, prefer transparent `letI` bindings or the default
  fold-left instances.
- Iterated disjunction definition classes are present because they are active
  Coq declarations, but the Coq L11 file does not provide fold constructors or
  proof-class conversion lemmas for them.

Guidance:

- Use `AddConnective_iter_andp` only in contexts where the and/true language
  and proof classes are already available.
- For direct use, prefer explicit `FoldLeftAnd2IterAnd`,
  `FoldRightAnd2IterAnd`, `IterAndFromDefToAX_L2L`, and
  `IterAndFromDefToAX_R2L` names.
- For custom iterated conjunction semantics, make the hidden
  `IterAndLanguage` dictionary explicit in theorem statements or provide
  matching local instances.

### L12 Classical Proof Theory

`PropositionalLogic/ProofTheory/Classical.v` is migrated as
`Unifysl.PropositionalLogic.ProofTheory.Classical`.

Current Lean shape:

- Public classes and theorem names are root `Unifysl.*` declarations:
  `ClassicalAxiomatization`, `ClassicalSequentCalculus`,
  `ClassicalDeduction`, `ClassicalPropositionalLogicEquiv`,
  `deduction_derived_neg`, and the corresponding rules and conversions.
- Registration instances extend the existing `ExtensionTactic` tables at the
  Coq indices: `P2D_reg` index `10` and `D2P_reg` index `8`.
- The implementation reuses the L11 `PeirceLaw`/`ByContradiction`/
  `DoubleNegElimination`/`ClassicAnalysis` conversion chain where possible.
- The implementation now reuses public minimal helpers from L8 and L11 instead
  of keeping local proof-helper duplicates in `Classical.lean`.

Resolved issues found during migration:

- The L8 helper-premise mismatch was fixed by exposing
  `solve_iffp_intros_minimal` and adding `impp2orp2_minimal`; L12 now uses
  those public helpers directly.
- The L11 helper visibility issue was fixed by exporting
  `Axiomatization2SequentCalculus_orpSC_minimal` and
  `Axiomatization2SequentCalculus_inegpSC_minimal`; L12 now uses the exported
  negation sequent-calculus helper directly.
- The review pass found that `Axiomatization2SequentCalculus_cpSC` originally
  had a stronger `DerivableProvable` premise than the Coq theorem. This was
  corrected to the Coq-aligned `ProvableDerivable` premise before validation.
- The literal smoke pattern `example : True := by AddSequentCalculus;
  infer_instance; trivial` is not a valid Lean proof shape, because
  `infer_instance` only solves a current typeclass goal. The equivalent
  validated shape is to run `AddSequentCalculus`, then bind the intended class
  explicitly with `have _ : ClassicalSequentCalculus L
  (inferInstance : Derivable L) := inferInstance`, then close `True`.

Risk:

- Future files that copy Coq tactic smoke tests verbatim may hit the same
  `infer_instance` target-shape issue.

Guidance:

- Keep new classical registrations in the module that owns the corresponding
  theorem, following the L8 and L12 pattern.
- For Add* tactic validation on a non-typeclass goal, explicitly bind the
  intended synthesized class with `have _ : ... := inferInstance`.

### L13 CoqProp And Propositional Predicate Layer

The following modules are migrated:

- `MetaLogicInj/ProofTheory/ProofRules.v`
- `PropositionalLogic/ProofTheory/TheoryOfPropositionalConnectives.v`
- `PropositionalLogic/ShallowEmbedded/PredicatePropositionalLogic.v`

Current Lean shape:

- Coq-prop proof classes and rules are root `Unifysl.*` declarations, with
  `D12P_reg` entries at Coq indices `8` and `9`.
- `AddConnective_iffp`, `AddConnective_truep`, `AddConnective_negp`, and
  `AddConnective_truep_impp_self` are Lean tactics that add local instance
  hypotheses for the derived language dictionary, definition witness, and
  proof-class conversion.
- `Pred_Gamma` is preserved as a Coq-named instance with lower priority because
  its semantics matches the existing `Pred_strongGammaP` instance.

Resolved issues found during review:

- `CoqPropSequentCalculus.derivable_coq_prop_impp_left` was corrected to the
  Coq left-rule shape `Phi ;; ((!! P) ⟶ (!! Q)) |--- !! (P -> Q)`.

Risk:

- The `AddConnective_*` tactics follow Lean local-instance mechanics rather
  than Coq `set`/`clearbody` proof-term visibility. The observable behavior is
  that later instance search sees the derived dictionaries and proof classes.
- `Pred_Gamma` and `Pred_strongGammaP` intentionally coexist; the lower
  priority on `Pred_Gamma` avoids changing existing default instance choices.

Guidance:

- Validate connective tactics by checking the intended class with
  `inferInstance` after the tactic runs.
- Prefer explicit `Pred_Gamma A` only when matching Coq names matters in a
  theorem statement.

### L14 Separation Proof Theory

`SeparationLogic/ProofTheory/SeparationLogic.v` is migrated as
`Unifysl.SeparationLogic.ProofTheory.SeparationLogic`.

Current Lean shape:

- Separation proof-theory classes and active D1/provable conversion lemmas are
  root `Unifysl.*` declarations.
- The Coq D1 cancel proof block has no Lean declarations because it is inside a
  Coq comment block. The provable-level cancel lemmas are migrated.
- Logic-equivalence lemmas use explicit `logic_equiv` forms in the Lean source;
  direct Coq-style token spelling would conflict with Lean comment lexing.
- Review found that Coq `:>` parent-class behavior for
  `MallocFreeSeparationLogic` needed explicit Lean instances; these instances
  are now provided in the L14 module.

Risk:

- No L14 blocker is currently recorded.
- Later separation proof-theory layers may require additional helper lemmas for
  rewriting through sepcon/wand expressions, but L14 did not require dependency
  module changes.

Guidance:

- Keep future separation proof registrations in their owning modules; L14 has
  no active Coq registration entries.
- For statement comparisons, treat explicit `logic_equiv x y` applications as
  the Lean-side surface form of Coq equivalence notation.

### L15 Separation Axiom Theory

`SeparationLogic/ProofTheory/TheoryOfSeparationAxioms.v` is migrated as
`Unifysl.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms`.

Current Lean shape:

- The weak sepcon/emp rule classes and adjointness-derived conversion lemmas
  are root `Unifysl.*` declarations.
- The Lean proofs reuse the existing provable-level proof-pattern namespaces
  and L14 separation proof-theory lemmas.
- This Coq file has no active proof-registration entries, so no Lean register
  table additions were made.

Risk:

- No L15 blocker is currently recorded.

Guidance:

- Keep future deduction-level conversions in the later deduction module; L15
  only covers provable-level rule conversions.

### L16 Separation Deduction And Predicate Embedding

`SeparationLogic/ProofTheory/Deduction.v` is migrated as
`Unifysl.SeparationLogic.ProofTheory.Deduction`.
`SeparationLogic/ShallowEmbedded/PredicateSeparationLogic.v` is migrated as
`Unifysl.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic`.

Current Lean shape:

- Deduction-level separation conversions, weak deduction/equiv classes, and
  `D12P_reg` entries 10 through 19 are provided.
- Predicate separation instances use weak sepcon/wand semantics and the
  existing flat soundness theorems.
- Coq has repeated leaf names across different proof-theory files. The Lean
  root namespace already owns those names from earlier layers, so the L16
  versions are available at
  `Unifysl.SeparationLogic.ProofTheory.Deduction.Axiomatization2Deduction_sepconD`,
  `.Adj2SepconMono`, and `.Adj2SepconFalse`.
- `AddAxiomatizationFromDeduction` finds the L16 separation registrations after
  the usual deduction bridge prerequisites are present; in particular the
  earlier `D12P_reg` bridge for `Derivable1Provable` needs the basic minimum
  and conjunction deduction classes.

Risk:

- No L16 blocker is currently recorded.

Guidance:

- Prefer the module-qualified L16 names when downstream Coq code refers
  specifically to declarations from `Deduction.v`.
- For tactic checks, include the same bridge prerequisites that Coq instance
  search used before expecting separation registrations to fire.

### L17 Separation Rewrite And Shallow Model Builders

`SeparationLogic/ProofTheory/RewriteClass.v` is migrated as
`Unifysl.SeparationLogic.ProofTheory.RewriteClass`.
`SeparationLogic/ShallowEmbedded/Join2Sepcon.v` is migrated as
`Unifysl.SeparationLogic.ShallowEmbedded.Join2Sepcon`.
`SeparationLogic/ShallowEmbedded/Model2CoqPropEmp.v` is migrated as
`Unifysl.SeparationLogic.ShallowEmbedded.Model2CoqPropEmp`.

Current Lean shape:

- Separation rewrite/proper instances are root `Unifysl.*` instances, matching
  the Coq exported instance names.
- Existing minimum/propositional rewrite relation helpers are private in their
  owning Lean files. The separation rewrite file therefore defines private
  same-semantics relation aliases locally.
- Shallow embedded model builders use module-qualified namespaces for generic
  section names such as `Model_L`, `L`, `SM`, and `GammaD1_*`, avoiding root
  namespace pollution and duplicate names across the two Coq files.
- Coq source comment blocks with former or alternative definitions were not
  migrated.
- In `Join2Sepcon`, proof-theory class construction needs explicit local
  `letI` bindings for the language/proof class instances. This is a Lean
  elaboration surface difference only.
- In `Model2CoqPropEmp`, the Coq source has a cross-section-looking
  `GammaD1_tt` construction shape. Lean implements the intended target section
  language `L_tt`, with the same pointwise implication relation.

Risk:

- No L17 blocker is currently recorded.

Guidance:

- Downstream modules should refer to shallow builder declarations through their
  module-qualified namespaces unless a root alias is explicitly added later.
- Do not expose the private rewrite relation aliases as public API unless a
  later module has a concrete need for shared rewrite relation names.

### L18 Separation Derived Rules, Cancel, And Corable

`SeparationLogic/ProofTheory/DerivedRules.v` is migrated as
`Unifysl.SeparationLogic.ProofTheory.DerivedRules`.
`SeparationLogic/ProofTheory/TheoryOfCancel.v` is migrated as
`Unifysl.SeparationLogic.ProofTheory.TheoryOfCancel`.
`SeparationLogic/ProofTheory/Corable.v` is migrated as
`Unifysl.SeparationLogic.ProofTheory.Corable`.

Current Lean shape:

- Derived separation rules are root `Unifysl.*` declarations.
- `TheoryOfCancel` preserves the Coq cancel data structures and recursive
  marking/restoration algorithm, using the existing migrated `PTree` and
  `positive` encoding.
- Root `Unifysl.sepcon_assoc2` already exists from the base separation proof
  theory. The `TheoryOfCancel.v` lemma with the same leaf name is therefore
  available at
  `Unifysl.SeparationLogic.ProofTheory.TheoryOfCancel.sepcon_assoc2`.
- Coq `Pos.succ` is represented by a private structurally recursive
  `positive_succ` in `TheoryOfCancel`.
- `Corable` keeps the Coq field name `corable_preserved'`; Lean accepts the
  trailing apostrophe.
- Several proof scripts that used Coq rewrite automation are represented by
  explicit proof composition and private local helper lemmas.
- Source relocation notes in `DerivedRules.v` were not copied as active Lean
  declarations.

Risk:

- No L18 blocker is currently recorded.

Guidance:

- Prefer the module-qualified cancel lemma name when the intended source is
  specifically `TheoryOfCancel.v`.
- Keep `positive_succ` private unless a later module needs the same Coq
  positive successor operation.
- If later modules need the local proof helpers from `DerivedRules` or
  `Corable`, expose only the smallest reusable lemma in the owning module
  rather than changing existing statement prerequisites.

### L19 Iterated Separation Conjunction

`SeparationLogic/ProofTheory/IterSepcon.v` is migrated as
`Unifysl.SeparationLogic.ProofTheory.IterSepcon`.

Current Lean shape:

- The active iterated-sepcon classes, deduction-to-axiomatization bridge,
  fold-left/fold-right constructors, normality lemmas, iterated-wand
  constructor, and `D12P_reg` entry `20` are available at root
  `Unifysl.*` names.
- The fold-based constructors and normality lemmas remain definitions/theorems,
  not exported global default instances. This keeps instance synthesis closer
  to Coq's tactic-local construction behavior.
- `iter_sepcon_unfold_right_assoc` uses the existing Lean helper
  `fold_right_prodp_no_unit` to represent the same singleton-preserving
  right-associated fold that Coq writes as an inline `fix`.
- `AddConnective_iter_sepcon` follows the existing Lean
  connective tactic pattern: it inserts local instance hypotheses for the
  fold-left iter-sepcon language, definition witness, and axiomatization
  instance in the current local context. This preserves downstream
  `infer_instance` and theorem-application behavior, while not reproducing Coq
  Ltac's `set`/`clearbody` proof-context operations literally.
- In smoke tests, the tactic-level `infer_instance` form sees the instances
  inserted by `AddConnective_iter_sepcon`. The term form `inferInstance` may
  fail in immediately following anonymous `have` terms, so local tests should
  use `by infer_instance` when checking these generated instances.
- The file adds private local helper lemmas for iff transitivity/symmetry and
  sepcon unit instances so the proof does not require changes to earlier
  modules.

Risk:

- No L19 blocker is currently recorded.

Guidance:

- Downstream generated interfaces can use `AddConnective_iter_sepcon` in the
  same style as `AddConnective_iter_andp`, provided the local context has a
  single `Language` and a single matching `Provable`.
- If a later module requires the exact inline right-fold expression rather
  than `fold_right_prodp_no_unit`, add a small conversion lemma in the owning
  module instead of changing the L19 public theorem.

### L20 Shallow Quantifier Proof Theory

`ShallowQuantifierLogic/ProofTheory.v` is migrated as
`Unifysl.ShallowQuantifierLogic.ProofTheory`.

Current Lean shape:

- The shallow existential and universal deduction classes are available at
  root `Unifysl.*` names.
- The active existential-and, existential-sepcon, iterated-sepcon flatten,
  iterated-sepcon existential, sepcon/meta-proposition interaction, and
  iterated-sepcon/meta-proposition classes and derived lemmas are available at
  root `Unifysl.*` names.
- Coq's local `derivable1_sepcon_assoc2` leaf name conflicts with an existing
  root theorem from the separation proof theory. The L20 compatibility alias is
  therefore available as
  `Unifysl.ShallowQuantifierLogic.ProofTheory.derivable1_sepcon_assoc2`.
- Coq rewrite scripts are represented by explicit `derivable1_trans`,
  `derivable1_*_adjoint`, and monotonicity compositions. This is a proof-script
  surface difference only.
- The exploratory source comment blocks at the end of the Coq file were not
  migrated as active Lean declarations.

Risk:

- No L20 blocker is currently recorded.

Guidance:

- When downstream modules need the L20 association lemma by source identity,
  use the module-qualified alias above. For ordinary separation associativity,
  prefer the existing root `Unifysl.derivable1_sepcon_assoc2`.
- The `deduction_exp_and`, `deduction_exp_sepcon`, `IterSepconFlatten`,
  `sepcon_andp_prop`, `sepcon_andp_prop_ext`, and
  `Iter_sepcon_andp_prop` classes are section-parameterized in Lean; use
  explicit `(L := ...)` only when inference cannot recover the language.

### L21 Shallow Quantifier Model Constructors

`ShallowQuantifierLogic/ModelConstrALL.v` is migrated as
`Unifysl.ShallowQuantifierLogic.ModelConstrALL`.
`ShallowQuantifierLogic/ModelConstrEX.v` is migrated as
`Unifysl.ShallowQuantifierLogic.ModelConstrEX`.

Current Lean shape:

- `AllpDefinition_Model`, `model2all`, `Model2All`,
  `Model2Allp_Normal`, `allL`, `GammaD1`, and `Model2AllDeduction`
  are available under `Unifysl.ShallowQuantifierLogic.ModelConstrALL`.
- `ExpDefinition_Model`, `model2exp`, `Model2Exp`,
  `Model2Exp_Normal`, `expL`, `GammaD1`, and `Model2ExpDeduction`
  are available under `Unifysl.ShallowQuantifierLogic.ModelConstrEX`.
- The generic Coq section names `Model_L`, `allL`, `expL`, and `GammaD1`
  are kept module-qualified rather than exported to root, avoiding conflicts
  with other shallow model-construction modules that use the same leaf names.
- The Coq section parameter `{M : Model}` is represented explicitly as an
  argument to the corresponding Lean constructors and instances.

Risk:

- No L21 blocker is currently recorded.

Guidance:

- Downstream modules should refer to the model constructors with their module
  qualifiers, for example
  `Unifysl.ShallowQuantifierLogic.ModelConstrEX.Model2ExpDeduction`.
- If a later generated interface expects a root leaf name, add a small local
  alias in that interface layer instead of exporting these generic names from
  L21.

### L22 demo932 Interface

`LogicGenerator/demo932/Interface.v` is migrated as
`Unifysl.LogicGenerator.demo932.Interface`.

Current Lean shape:

- Coq module types are represented by Lean structures and namespaced
  definitions: `LanguageSig`, `DerivedNamesSig`, `PrimitiveRuleSig`,
  `LogicTheoremSig`, and `LogicTheoremSig'`.
- `PrimitiveRuleSig` and `LogicTheoremSig` assumptions are structure fields,
  not global axioms.
- `LogicTheoremSig'` extends `LogicTheoremSig`; its `default` constructor
  rebuilds the Coq `#[export] Instance` environment with local `letI` bindings
  and fills the fields from the migrated L0-L21 infrastructure.
- The migrated `PTree` module is currently top-level, so `Interface.lean`
  exposes a local `Unifysl.LogicGenerator.demo932.positive` alias for
  `PTree.positive`.
- Coq exported instance names beginning with `_` are represented by Lean-safe
  `*_inst` fields inside `LogicTheoremSig'`.
- The commented `IPSolver` source block is intentionally outside the active
  Lean API.

Risk:

- No L22 blocker is currently recorded.

Guidance:

- Downstream consumers should import `Unifysl.LogicGenerator.demo932.Interface`
  and refer to the public interface names under
  `Unifysl.LogicGenerator.demo932`.
- If a future target expects Coq's exact functor/module syntax, wrap these
  structures at that target layer rather than changing the L22 structure API.

### Local Standard-Library Compatibility Helpers

The migration intentionally avoids mathlib. Some Coq standard-library helpers
are reimplemented locally.

Examples:

- list `Forall`/`Forall2` helpers
- relation-pair compatibility definitions
- set/ensemble compatibility definitions
- private proof helpers inside larger proof-theory files

Risk:

- Later modules may need additional Coq compatibility lemmas not yet exposed.

Guidance:

- Add compatibility helpers in the smallest owning module.
- Do not change existing public definitions just to simplify a downstream proof.
