# Working Rules

**Author**: Agent team
**Date**: 2026-06-12

## Principle: First Discuss, Then Modify

1. **Discuss before coding.** Before making any significant change — whether adding a new lemma, changing a definition, or modifying a proof strategy — first propose the approach and get confirmation.

2. **No unilateral commits.** Commits are only made when the user explicitly says "commit" or "Commit the changes" or similar. Do not commit just because the work looks complete.

3. **Explain the problem.** When stuck (compilation error, proof blockage), explain the root cause and possible fixes before attempting one. If multiple options exist, present them and ask for direction.

4. **Keep the user informed.** After each significant change, summarize what was done, what changed, and what the next step is.

5. **Admitted is a temporary marker.** A lemma marked `Admitted` means "the definition is agreed upon, the proof is deferred." Before marking anything `Admitted`, explain why and when it will be proved.

## Retry Limit & Cooperation

1. **Max 5 retries per goal.** If an agent retries a proof attempt more than 5 times without making progress, it must stop and report the problem.
2. **Escalate to the user.** On the 6th failure, the agent clearly states: the goal, what was tried, why each attempt failed, and any suspected root cause.
3. **User provides context.** The user will use `vscoqtop` to inspect the goal state and share the full context (hypotheses, goal, environment). The agent then resumes based on that information.

## rocq-mcp Usage

When debugging Rocq proofs interactively, always use `rocq-mcp` (not `coqc`) for fast iteration:

1. Start `rocq-mcp` with the correct workspace flags matching the `_CoqProject` or makefile flags.
2. Use `rocq_start` to begin an interactive session on the target `.v` file.
3. Use `rocq_start` with `line` and `character` to jump to error positions.
4. Use `rocq_query` to inspect the current context (hypotheses, goal).
5. Use `rocq_check` with `from_state` for step-by-step tactic execution.
6. Use `coqc` only for full-project rebuilds and final verification.

The MCP server is at `mcp/rocq-mcp/.venv/bin/rocq-mcp`. The workspace is the repo root with `_CoqProject` providing load paths.

---

## Proof Discipline

### SCC.v Rules (fully proved)

- All lemmas in `SCC.v` must be fully proved, no `Admitted`.
- The file compiles cleanly with `make Kosaraju/SCC.vo`.
- `StepUniqueDirected` is needed (added via `KosarajuGraph` bundling Graph, GValid, StepValid, StepUniqueDirected, FiniteGraph together).

### Kosaraju.v Rules (definitions + admitted proofs)

- Definitions: `St`, `visit1`, `visit2`, `set_finish`, `set_scc_id`, `DFS_finish_f`, `DFS_finish`, `DFS_scc_f`, `DFS_scc`, `pick_unvisited1`, `pick_unvisited2`, `kosaraju_finish_f`, `kosaraju_finish`, `kosaraju_scc_f`, `kosaraju_scc`, `kosaraju`.
- Lemma signatures must be declared before their proofs are filled in.
- Phase 1 lemmas follow the C10909 pattern.
- Phase 2 lemmas are not yet written.

### Proof Order

```
SCC.v (done)
    ↓
Phase 1 lemmas (DFS_finish_visited_incr, DFS_finish_visited_self,
                DFS_finish_reachable_rev, DFS_finish_finish_after,
                kosaraju_finish_visited_all, kosaraju_finish_order)
    ↓
Phase 2 lemmas (DFS_scc_visited_incr, DFS_scc_same_root,
                DFS_scc_reachable, kosaraju_scc_correct, etc.)
    ↓
Composition (kosaraju_correct)
```

---

## Coq 8.20 Workarounds

`St` is an `Inductive` (non-primitive) record to avoid Coq 8.20 primitive record restrictions. However, `subst` may still fail if the variable appears in hypotheses through projections. Use `rewrite` instead of `subst` where possible.

---

## File Structure

```
SeparationLogic/algorithms/Kosaraju/
├── SCC.v        — SCC graph theory (608 lines, fully proved)
├── Kosaraju.v   — Monadic program + proofs (398 lines, DFS_finish_visited_incr proved)
└── makefile     — Adds Kosaraju_FILES to build

SeparationLogic/GraphLib/          — Graph type classes and lemmas
SeparationLogic/MonadLib/          — State-relational monad + Hoare logic
SeparationLogic/sets/              — SetsClass set theory library
```

---

## Induction on Indexed Types

Proving properties over `reachable_rev` (or any `Inductive` with an index in `V -> Prop`) by `induction` often fails because Coq's dependent induction generalizes **every hypothesis mentioning the index**. This pollutes the induction hypothesis with irrelevant premises.

### Preferred approach: use `refine` + `fix`

Instead of `induction`, manually construct a recursive function with `fix`:

```coq
refine ((fix f (x : A) (H : P x) {struct H} : Q x :=
  match H with
  | C1 a b => ...
  | C2 a b Hsub => ... f ... Hsub ...
  end) init_x init_H).
```

- `fix` does **no** automatic generalization — only the explicitly passed arguments appear in the IH.
- `{struct H}` tells Coq which argument is structurally decreasing.
- The `match` branches must each be a single Coq **term**, not tactic blocks.
- If you need to convert types inside a branch (e.g. `SCC.step_rev` vs local `step_rev`), nest another `match` rather than using `unfold` (which is a tactic).

### `classic` returns `\/`, not `sumbool`

`Coq.Logic.Classical_Prop` exports `classic P` of type `P \/ ~P`. Match with `or_introl` / `or_intror`, **not** `left` / `right`.

### When `induction` is fine

- The index does **not** appear in any other hypothesis of the current goal.
- The property is simple enough that the auto-generated IH is usable without cleaning.
- If you must use `induction`, consider `generalize dependent` first to remove all side hypotheses that mention the index, then `intros` them back after the induction. But this often fails when the index appears in a hypothesis that also binds other variables (like `reachable_rev v w` where both `v` and `w` are shared). In such cases, `fix` is always safer.

---
