# Kosaraju.v — Kosaraju's Algorithm: Monadic Definition and Correctness Proof

**Source**: `SeparationLogic/algorithms/Kosaraju/Kosaraju.v` (3137 lines)

## Overview

Defines Kosaraju's two-pass SCC algorithm as a nondeterministic monadic program in `StateRelMonad`, then proves its total correctness via Hoare-logic reasoning and least-fixed-point (`Lfix`) induction. The final theorem establishes that `scc_id` equality coincides with mutual reachability.

```
kosaraju_correct :
  Hoare (st = init_st) kosaraju
    (fun _ s' =>
       (forall v, visited2 s' v) /\
       (forall u v, scc_id s' u = scc_id s' v <-> mutually_reachable u v))
```

## Graph Requirements

```
Class KosarajuGraph (G V E : Type) := {
  kos_graph    :: Graph G V E;
  kos_gvalid   :: GValid G;
  kos_stepvalid :: StepValid G V E;
  kos_unique   :: StepUniqueDirected G V E;   (* edge uniqueness *)
  kos_finite   :: FiniteGraph G V E;
}.
```

## Program State

Non-primitive inductive record (avoids Coq 8.20 primitive record restrictions):

| Field | Type | Purpose |
|-------|------|---------|
| `timer` | `nat` | Monotonically increasing clock |
| `finish` | `V -> nat` | Finish time per vertex (Phase 1) |
| `visited1` | `V -> Prop` | Visited set for Phase 1 (reverse DFS) |
| `visited2` | `V -> Prop` | Visited set for Phase 2 (forward DFS) |
| `scc_id` | `V -> nat` | SCC label per vertex (Phase 2) |
| `scc_next` | `nat` | Next fresh SCC label |

## Program Definition

### Phase 1 — Reverse-Graph DFS with Finish Times

- **`DFS_finish_f W u`**: One-step body. Visit `u`, explore reverse edges (`step_aux g e v u`), recurse via `W v`, then `set_finish u (timer)` at break.
- **`DFS_finish u`**: `Lfix DFS_finish_f u`.
- **`kosaraju_finish`**: Outer loop. Repeatedly pick an unvisited vertex, run `DFS_finish`, until all visited.

### Phase 2 — Forward-Graph DFS with SCC Labeling

- **`DFS_scc_f root W u`**: Visit `u`, assign `scc_id[u] := scc_id[root]`, explore forward edges (`step_aux g e u v`), recurse via `W v`.
- **`DFS_scc root u`**: `Lfix (DFS_scc_f root) u`.
- **`kosaraju_scc`**: Outer loop. Pick unvisited vertex with max finish time, assign fresh `scc_id`, run `DFS_scc`, repeat.

### Full Algorithm

```
kosaraju := kosaraju_finish ;; kosaraju_scc
```

## Proof Structure

### Section 0: Hoare Helpers

- `Hoare_normalize`: lift pointwise Hoare triple to general precondition.
- `Hoare_normal_assume_bind`: assume-guard elimination.
- `Hoare_normal_LFix`: Lfix induction principle (no precondition on initial state).
- `Hoare_normal_LFix_closed`: Lfix induction with a state-invariant `R` closed under the recursive step.
- `Hoare_imp_post`, `Hoare_conj`: postcondition weakening and conjunction.

### Section 1: State Primitive Lemmas

Hoare lemmas for `visit1`, `visit2`, `set_finish`, `set_scc_id`, `set_scc_root_id`.

### Section 2: Phase 1 Inner DFS Properties

All proved via `Hoare_normal_LFix` with tailored `Q` and `P_loop`:

| Lemma | Property |
|-------|----------|
| `DFS_finish_visited_incr` | `visited1 s0 ⊆ visited1 s'` |
| `DFS_finish_visited_self` | `visited1 s' u` |
| `DFS_finish_step_visited` | All `step_rev` neighbors of `u` are visited |
| `DFS_finish_neighbor_visited_strong` | New vertices are either old or `step_rev`-neighbor-closed |
| `DFS_finish_reachable_rev` | New vertices satisfy `reachable_rev u v` |
| `DFS_finish_Q_after` | Compound: visited monotonicity, finish ordering, timer monotonicity |
| `DFS_finish_preserves_TimerDominates` | `TimerDominates` (finish < timer for visited) preserved |
| `DFS_finish_preserves_ReachRevClosed` | `ReachRevClosed` (visited closed under `reachable_rev`) preserved |
| `DFS_finish_step_rev_closed` | All new vertices are `step_rev`-closed |
| `DFS_finish_finish_ge_timer` | New vertices have finish >= entry timer |
| `visited_boundary_not_closed` | Path from visited to unvisited crosses a non-`step_rev`-closed vertex |

### Section 3a: Phase 1 — Phase1_Order for a Single DFS Tree

The key lemma closing the last `Admitted` in the proof:

```
Definition R_non_closed u st :=
  forall v, visited1 st v ->
    ~(forall w, step_rev v w -> visited1 st w) ->
    reachable_rev v u.

Definition Q_phase1 u' s0' _ s' :=  (* 11 conjuncts *)
  visited1 monotonicity /\ self-visited /\ step_rev_closed (incl. root) /\
  reachable_rev from root /\ finish < timer /\ old finish preserved /\
  timer monotonicity /\ non-root finish < root finish /\ finish >= entry timer /\
  (R_non_closed preserved) /\ (Phase1_Order for new vertices)
```

- **`DFS_finish_phase1`**: Compound Lfix proving all 11 conjuncts. The Phase1_Order conjunct uses a **disjunctive P_loop** (witness is either a concrete non-root vertex, or the root with `finish < timer` deferred to break). Four cases in the continue branch:
  - **Same subtree**: W's IH.
  - **a earlier, b later** (cross-subtree): boundary crossing + R -> `mutually_reachable a u'`, witness `c = u'`.
  - **b earlier, a later**: timer ordering -> `finish b < finish a`, witness `c = a`.
  - **Both from W**: W's Phase1_Order output.

- **`DFS_finish_finish_unvisited`**: DFS preserves finish of unvisited vertices.

### Section 3: Phase 1 Outer Loop

- `kosaraju_finish_visited_all`: After `kosaraju_finish`, all vertices are `visited1`.
- **`kosaraju_finish_phase1_order`**: `Phase1_Order` holds after Phase 1. Proved via `Hoare_normal_LFix_closed` with invariant:
  ```
  Inv s := ReachRevClosed s /\ TimerDominates s /\
           (unvisited finish = 0) /\ Phase1_Order_vis s
  ```
  Per-iteration case analysis:
  - **Old-old**: finish preserved + old Phase1_Order.
  - **Old->new**: impossible (`ReachRevClosed` blocks `reachable_rev` from old to new).
  - **New->old**: timer ordering (`finish_old < timer <= finish_new`), witness `c = a`.
  - **New-new**: `DFS_finish_phase1` conjunct 11 (R vacuously satisfied).

### Section 4: Phase 2 Inner DFS Properties

Mirrors Phase 1 structure for forward-graph DFS:

| Lemma | Property |
|-------|----------|
| `DFS_scc_visited_incr` | `visited2 s0 ⊆ visited2 s'` |
| `DFS_scc_step_visited` | Forward neighbors visited |
| `DFS_scc_neighbor_visited_strong` | New vertices neighbor-closed |
| `DFS_scc_reachable_from_u` | New vertices reachable from `u` |
| `DFS_scc_preserves_ForwardReachClosed` | `ForwardReachClosed` preserved |
| `DFS_scc_reachable_visited_closed` | Under `ForwardReachClosed`, DFS visits all reachable |
| `DFS_scc_mutually_reachable_root` | Under `Phase1_Order` + max-finish, new vertices are mutually reachable with root |
| `DFS_scc_visits_scc` | DFS visits the entire SCC of root |
| `DFS_scc_same_root_id` | All new vertices get same `scc_id` as root |
| `DFS_scc_R` | Combined: DFS preserves the `R` invariant |

### Section 5: Phase 2 Outer Loop and Final Assembly

- `kosaraju_scc_all_visited`: After `kosaraju_scc`, all vertices are `visited2`.
- `kosaraju_scc_preserves_ForwardReachClosed`, `kosaraju_scc_preserves_R`: Outer loop maintains invariants.
- `kosaraju_finish_R`: Phase 1 establishes the `R` invariant.
- **`kosaraju_correct`**: Final assembly via `Hoare_bind` of Phase 1 (`kosaraju_finish_R`) and Phase 2 (`kosaraju_scc_preserves_R` + `kosaraju_scc_all_visited`).

## Key Definitions

| Name | Meaning |
|------|---------|
| `ReachRevClosed s` | `visited1 s` closed under `reachable_rev` |
| `ForwardReachClosed s` | `visited2 s` closed under `reachable g` |
| `TimerDominates s` | All visited vertices have `finish < timer` |
| `R_non_closed u st` | Non-`step_rev`-closed visited vertices can `reachable_rev` to `u` |
| `Phase1_Order s` | Condensation-DAG finish ordering: `reachable_rev a b /\ ~reachable_rev b a -> exists c, mutually_reachable a c /\ finish b < finish c` |
| `R s` (Phase 2) | `ForwardReachClosed /\ Phase1_Order /\ all visited1 /\ scc_id < scc_next /\ (scc_id equal <-> mutually_reachable)` |

## Dependencies

- `MonadLib.StateRelMonad`: `StateRelBasic`, `StateRelHoare`, `FixpointLib`
- `GraphLib`: `graph_basic`, `reachable_basic`
- `Algorithms.Kosaraju.SCC`
- `SetsClass.SetsClass`
- `Coq.Logic.Classical_Prop`
