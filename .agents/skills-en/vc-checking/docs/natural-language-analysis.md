# Natural-Language Proof Analysis

Natural-language analysis records provability, proof-mode rationale, concrete proof strategy, a second load/coupling review, public-helper ownership, and group boundaries in `agent_output.md`. The controller does not parse a fixed format from it. Machine acceptance comes from the current version, group plan, conditional reuse hints, group validation, parent verification, and final-check.

## Reading order

1. `agent_input.md`: version, target witnesses, group bound, and output paths.
2. Raw `*_proof_manual.v`: top-level VCs and their `<vc>_split_goal_*` obligation source, mapping, and order.
3. Goal/auto/check files: read-only theorem expansion.
4. Current `formal_case_lib`.

Do not read or create another manual-preprocessing artifact.

Prefer references in `Rocq/examples/LLM_bench` and `QCP_demos_LLM`; human cases are non-authoritative idea sources only.

## Order of analysis

First traverse every split goal, recording only whether it is provable. Do not analyze any top-level VC or plan helpers, concrete proof routes, or reuse. If a top-level VC has at least one split goal and all are provable, select `aggressive_pre_process`. If any split goal is unprovable, or there is no split goal, judge only the whole top-level VC's provability; select `LLM_pre_process` if the whole goal is provable, and return an annotation/specification gap only if it is still unprovable.

After every `proof_mode` is fixed, write proof strategies and, when the handoff binds the immediately previous sealed vc-proving source, complete reuse comparison in the same step. For `aggressive_pre_process`, analyze and compare only split goals and ignore the top-level VC. For `LLM_pre_process`, analyze and compare only the whole top-level VC and ignore its split goals. Use the current/reference debug commands for each comparison unit, execute `Show.`, and collect controller script/combined-build-seal/version receipts. The combined build digest mechanically binds the local tree and the accepted dependency artifact digest. The source may be failed or may be a verified round made stale by annotation/freshness retry. Without a binding, write the detailed strategies directly and never scan history or create reuse hints.

## Questions for every analyzed goal

- Is `P |-- Q` semantically valid?
- What are the pre/post spatial, pure, and existential components?
- Which value instantiates each right-side witness?
- Which resources cancel directly, and which segments/lists require transformation?
- Which bounds, guards, length facts, and equalities does arithmetic use? Do not write only “lia.”
- What are the refinement hypothesis and target states, and which unfold/choice steps connect them?
- If a helper is needed, what is its statement, premises, source of every premise, and destination?
- On failure, is the gap in C annotations, `formal_case_lib`, stale files, or a malformed VC?

Use concise Markdown sections instead of filling a legacy JSON template. The content must be concrete enough to guide a group worker or annotation repair.

## Helpers

For `needs-helper`, state the helper shape, witnesses using it, how every premise is discharged from the current VC, and its owner `group_worker_lib` destination. Only a newly proved or adapted helper appears in the plan, with the owner suffix; a previous-round or public-snapshot helper with identical declaration/proof tokens is only an opportunistic reuse. Use `visibility: local` for a helper used only by this group. Use `visibility: public` for a stable mathematical property independent of concrete C locals and expected to be reusable in later groups or rounds; list likely consumers in notes. After owner validation passes, the controller appends the public helper and its necessary local-helper dependency closure to the durable pool for future rounds. A premise that cannot be discharged reveals an annotation/specification gap. A missing formal specification still returns to annotation; the public pool never substitutes for it.

## Group analysis

After proof-strategy analysis, form initial groups of top-level VCs by invariant, proof pattern, array/frame transformation, refinement transition, and helper family, then review every group again for load, coupling, and expected critical path. Never group a split goal independently; it follows its top-level VC. Group an aggressive top-level VC by the combined burden of all its split-goal strategies. Record at least top-level witness count, aggressive split-goal burden, expected helper-family count/complexity, mathematical libraries, proof-mode differences, program phase, sustained context, helper owner, and the final split/merge rationale. For a likely tail, decide whether final-result and transition/safety work are independent; split them when they are, otherwise explain the indivisible helper/context and plan formal/public helpers that can be supplied earlier. Roughly two to six witnesses per group is normally reasonable. Manual seed controls final witness order, while the plan controls group/helper merge order. This prose is human review/worker input, not an acceptance parser input.

The final `group_plan.json` keeps only group id, per-VC proof mode, aggressive `split_strategies`, an `LLM_pre_process` whole-goal `strategy`, 1–5 `estimated_difficulty`, and owner-suffixed planned helpers with visibility. An aggressive witness omits top-level `strategy`; an `LLM_pre_process` witness omits `split_strategies`. It stores no version, verified, or dependency field. Every group must be provable independently from the formal seed and the same public-candidate snapshot frozen at preparing. An indivisible proof-specific helper family determines grouping; producer promotion in this round changes no sibling's input. Never plan to read/import a sibling `group_worker_lib`, wait for pool updates, inject helpers directly, or duplicate a large helper family across groups.

When sealed-source reuse is enabled, each group's `reuse_hints/<group-id>.md` contains only the fixed five-column comparison table in the order all helpers, all aggressive split goals, all `LLM_pre_process` top-level VCs. Every non-from-scratch `Lines` value must cover a complete helper/proof declaration from its first through last line; a subrange inside the declaration is invalid even if it includes every tactic. A helper direct row cites an accepted source group's complete proved declaration and has no partial mode. A split/whole direct or partial row cites a compatible previous copied-manual proof block. Direct proof also requires an accepted source, complete route, and matching current/previous semantic goal fingerprint; rename-only may be direct. A changed fingerprint is partial with adapter/common-frame analysis, or from scratch. Structurally invalid failed groups are absent, and unaccepted groups never provide direct reuse. `agent_output.md` may summarize the judgment but does not copy the whole table or previous proof.

An unprovable split goal triggers whole-top-level analysis and does not block by itself. Only when that whole top-level VC is still `annotation-bug` or genuinely blocked must the round omit a complete plan that can enter proving. Put the corresponding status/blocker in the terminal report while retaining concrete analysis in `agent_output.md`. The main agent later reads it with the JSON report, completes blocker summary/reflection in the next annotation `agent_input.md`, and appends the summary plus original paths to the one annotation session.
