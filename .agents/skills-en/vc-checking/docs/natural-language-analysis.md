# Natural-Language Proof Analysis

Write natural-language analysis in `agent_output.md` to explain provability, proof mode, concrete strategy, helper ownership, and group boundaries. The controller accepts the strict plan and later proof checks; it does not parse this prose.

Read the current handoff, main-root manual, goal/auto files, current case library, and—on later attempts—the earlier vc-checking results listed by the handoff. The current manual is authoritative. Insert `Show.` only inside the handed-off debug copy's target proof body when needed and run the exact controller command; change no other proof or non-proof token, and create no extra manual or debug script.

First perform a structural scan of every top-level VC, prioritizing no-split whole goals and checking resource addresses, scalar equalities, existentials, and current/`@pre` bridges. Explain the scan outcome without machine-count attestations. A concrete countermodel in which P holds and Q fails returns an annotation/specification/dependency blocker immediately, before exhaustive split analysis.

After that scan passes, judge every split goal without analyzing whole top-level VCs or planning helpers. Choose `aggressive_pre_process` when a VC has split goals and all are provable. Otherwise judge the whole top-level VC and choose `LLM_pre_process` when it is provable. Only an unprovable whole goal yields an annotation/specification/dependency blocker.

After all modes are fixed, analyze aggressive split goals and LLM whole goals. Do not analyze witness reuse. A later attempt may reference earlier vc-checking conclusions, but must state what the current manual confirms or changes.

For every selected target, answer:

- Is `P |-- Q` semantically valid?
- What are the pre/post spatial, pure, and existential parts?
- Which right-side witness is instantiated?
- Which resources cancel and which list/segment transformations are needed?
- Which bounds, guards, lengths, and equalities support arithmetic?
- What are the source and target refinement states?
- What helper is needed, with which premises and use site?
- If it fails, which annotation, library, manual, or tool boundary is responsible?

Only new or materially changed helpers enter the plan and use the group suffix. A premise unavailable from the current VC signals an annotation/specification gap.

After strategies are complete, group top-level VCs by shared invariant, proof pattern, resource transformation, refinement transition, and helper family. Review load, coupling, and likely tail work separately. Split goals never form independent groups.

The final plan contains only group IDs, proof modes, aggressive `split_strategies`, LLM `strategy`, `estimated_difficulty`, and planned helpers. It contains no controller metadata, acceptance, dependency, or reuse fields.
