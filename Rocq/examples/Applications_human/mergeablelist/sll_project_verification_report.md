# sll_project Verification Report

Case: `Applications_human/mergeablelist/sll_project`

Summary:
- Promoted from `Applications_human/Project/mergeablelist` to `Applications_human/mergeablelist`.
- Refreshed `symexec` and `StrategyCheck` outputs for the promoted logical path.
- Repaired promoted-path hypothesis drift in manual witness proofs.
- Added the case to `Rocq/Makefile` and `run-example-linux.sh`.

Checks:
- `symexec`: passed.
- `StrategyCheck`: passed.
- `coqc sll_project_proof_manual.v`: passed.
- `coqc sll_project_goal_check.v`: passed.
- `make -C Rocq examples/Applications_human/mergeablelist/sll_project_goal_check.vo examples/Applications_human/mergeablelist/sll_project_strategy_goal_check.vo`: passed.
- Manual proof scan: no `Admitted.` or extra `Axiom`.

Timing:
- Total wall-clock time observed for this case: 1h5m33s (3933s).
- The entries below are recorded key command/subagent timings, not an exhaustive additive breakdown of the total wall-clock time.
- Initial Project `symexec`: 1s.
- Promoted `sll_project_lib.v` compile: 90s.
- Promoted strategy proof chain before manual: about 178s.
- `vc-proving` round 1: worker pipeline timed out after about 611s; target fallback compile 27s.
- `vc-proving` round 2: target split compile passed; full scratch advanced to next witness.
- `vc-proving` round 3: full scratch manual compile passed.
- Final manual plus goal check compile: 113s.
- Final Makefile target compile: 55s.
- Timing gap: the earlier draft omitted the full wall-clock total and did not fully account for orchestration overhead, subagent setup/teardown, repeated compile attempts, and waiting time between delegated proving rounds.

Notes:
- Worker-side Rocq MCP was not usable in exec mode for this case, so proving rounds used the documented `coqc` fallback in scratch.
- No helper lemmas were added to `sll_project_lib.v`.
