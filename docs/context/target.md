# Target

**Date**: 2026-06-15

## Current State

### Phase 1 inner DFS (DFS_finish) — 13/14 proved, 1 Admitted

Proved:
- `DFS_finish_visited_incr` ✅
- `DFS_finish_visited_self` ✅
- `DFS_finish_step_visited` ✅
- `DFS_finish_reachable_rev_aux` ✅
- `DFS_finish_reachable_rev` ✅
- `DFS_finish_neighbor_visited_aux` ✅
- `DFS_finish_neighbor_visited_strong` ✅
- `DFS_finish_neighbor_visited` ✅
- `DFS_finish_combined_post` ✅
- `DFS_finish_Q_after` ✅
- `DFS_finish_preserves_TimerDominates` ✅
- `DFS_finish_preserves_ReachRevClosed` ✅
- `DFS_finish_finish_ge_timer` ✅
- `DFS_finish_preserves_OrderInv` ✅

1 Admitted:
- `DFS_finish_Q_full` ⚠️ 1 sub-admit at line 998 (cross-callee reachable_rev impossibility in recursive branch; a is visited by a completed sibling DFS, b by current recursive call — must show sibling would have already visited b)

### Phase 1 outer loop (kosaraju_finish) — all proved

- `kosaraju_finish_visited_all_aux` ✅
- `kosaraju_finish_visited_all` ✅
- `kosaraju_finish_aux` ✅
- `kosaraju_finish_preserves` ✅
- `kosaraju_finish_order_init` ✅

(Previously listed `kosaraju_finish_order_aux` / `kosaraju_finish_order` were never written; their semantics — OrderInv holds globally after Phase 1 with all vertices visited — are already covered by `kosaraju_finish_order_init` + `kosaraju_finish_visited_all`. These are NOT blockers.)

### Phase 1 summary: 1 remaining Admitted (`DFS_finish_Q_full` sub-admit)

---

### Phase 2 inner DFS (DFS_scc) — 8/12 proved, 4 Admitted

Proved:
- `DFS_scc_visited_incr` ✅
- `DFS_scc_visited_self` ✅
- `DFS_scc_step_visited` ✅
- `DFS_scc_neighbor_visited_aux` ✅
- `DFS_scc_neighbor_visited_strong` ✅
- `DFS_scc_reachable_aux` ✅
- `DFS_scc_reachable_from_u` ✅
- `DFS_scc_reachable` ✅

Admitted:
- `DFS_scc_reachable_visited` ❌ line 1886 (reachable from u ∧ not visited ⇒ visited after DFS)
- `DFS_scc_visits_scc` ❌ line 1897 (visit entire SCC of root when root has max finish)
- `DFS_scc_mutually_reachable_root` ❌ line 1907 (newly visited ⇔ mutually reachable with root)
- `DFS_scc_same_root_id` ❌ line 1980 (new vertices get same scc_id as root) — has sub-admit

### Phase 2 outer loop (kosaraju_scc) — all proved

- `kosaraju_scc_all_visited_aux` ✅
- `kosaraju_scc_all_visited` ✅

---

### Total Correctness — 3/3 Admitted

- `kosaraju_correct` ❌ line 2038 (主定理: scc_id 等价于 mutually_reachable)
- `kosaraju_correct_soundness` ❌ line 2043 (same scc_id → mutually_reachable)
- `kosaraju_correct_completeness` ❌ line 2048 (mutually_reachable → same scc_id)

---

### Blocker Summary (按依赖序)

1. `DFS_finish_Q_full` sub-admit (Phase 1, 1 admit)
2. `DFS_scc_reachable_visited` (Phase 2)
3. `DFS_scc_visits_scc` (Phase 2)
4. `DFS_scc_mutually_reachable_root` (Phase 2)
5. `DFS_scc_same_root_id` (Phase 2)
6. 三个 `kosaraju_correct*` (依赖 1-5)

opencode -s ses_12f97dab2ffevfFP0Ii6Csmmpj