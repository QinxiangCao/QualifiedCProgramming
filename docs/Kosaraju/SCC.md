# SCC.v — Strongly Connected Component Infrastructure

**Source**: `SeparationLogic/algorithms/Kosaraju/SCC.v` (674 lines)

## Overview

Pure graph-theoretic library for strongly connected components, independent of any algorithm or monadic framework. Provides definitions, partition existence, condensation DAG acyclicity, reversed reachability, and head/tail SCC characterization. Parameterized over an abstract graph `(G, V, E)` with `Graph`, `GValid`, `StepValid`, and `FiniteGraph` typeclasses.

## Sections

### 1. Mutually Reachable (lines 21–48)

```
mutually_reachable u v := reachable g u v /\ reachable g v u
```

Properties: `mutually_reachable_refl`, `_sym`, `_trans`.

### 2. Strongly Connected Component (lines 50–98)

```
is_SCC s :=
  (exists v, s v /\ vvalid g v) /\                   (* non-empty *)
  (forall u v, s u -> s v -> mutually_reachable u v) /\ (* internal connectivity *)
  (forall u v, s u -> vvalid g v -> mutually_reachable u v -> s v)  (* maximality *)
```

Key lemmas:
- `is_SCC_vvalid`: membership implies vertex validity.
- `is_SCC_closed_under_mr`: SCCs are closed under mutual reachability.
- `is_SCC_maximal`: if one SCC is a subset of another, they are equal.

### 3. SCC Partition (lines 100–221)

```
scc_partition sccs :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\  (* coverage *)
  (forall s, In s sccs -> is_SCC s) /\                      (* each is SCC *)
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2)  (* disjointness *)
```

- `equiv_class v`: the equivalence class `{w | vvalid g w /\ mutually_reachable v w}`.
- `equiv_class_is_SCC`: each equivalence class is an SCC.
- `scc_partition_exists`: an SCC partition exists (constructive, using `listV g`).

### 4. Condensation DAG Acyclicity (lines 223–398)

Defines `condensation_edge` (cross-SCC edge) and `condensation_reachable` (transitive closure).

- `condensation_reachable_implies_reachable`: condensation-path between different SCCs implies vertex-level reachability.
- `no_cycle_between_different_SCCs`: no two distinct SCCs can mutually reach each other.
- `condensation_is_acyclic`: a condensation edge `s1 -> s2` precludes `condensation_reachable s2 s1`.
- `vertex_reachable_condensation`: vertex-level reachability implies same SCC or condensation-reachability.

### 5. Reversed Graph Reachability (lines 400–462)

```
step_rev x y := step g y x
Inductive reachable_rev u : V -> Prop :=
  | rr_refl : reachable_rev u u
  | rr_step v w : step_rev u v -> reachable_rev v w -> reachable_rev u w
```

- `reachable_iff_reachable_rev`: `reachable g x y <-> reachable_rev y x`.
- `mutually_reachable_rev_equiv`: reversed mutual reachability is equivalent to forward mutual reachability.

### 6. Head and Tail SCCs (lines 464–673)

- **Tail SCC**: no outgoing condensation edge. Closed under forward reachability (`tail_SCC_closed_under_reachable`).
- **Head SCC**: no incoming condensation edge. Closed under backward reachability (`head_SCC_closed_under_reachable`).
- `tail_scc_iff_reachable_stays` / `head_scc_iff_reachable_stays`: equivalence between head/tail property and reachability closure.
- `condensation_edge_rev_iff`: reversed condensation edges correspond to forward condensation edges with swapped endpoints.
- `is_tail_SCC_rev_is_head` / `is_head_SCC_rev_is_tail`: duality between head and tail under edge reversal.

## Dependencies

- `GraphLib.graph_basic`, `GraphLib.reachable.reachable_basic`, `GraphLib.reachable.reachable_restricted`
- `SetsClass.SetsClass`
- `Coq.Logic.Classical`
