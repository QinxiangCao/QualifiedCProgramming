---
name: final-check
description: Use from the main agent after final-apply has written the accepted proving_merged result back to main root; verify consistency among generated files, manual, formal_case_lib, versions, merge result, and cleanup.
---

# Final Check

## When to invoke

Only the main agent invokes this skill after the controller has completed `final-apply`; no subagent is created. If final-check fails and rollback succeeds, follow the controller action and perform `final-apply` again before another final-check.

A human starts the public boundary with the root uv/Python 3.12 environment. Here, main executes only the action argv beginning with the validated absolute `sys.executable`; it does not wrap final-check in uv again.

## Broad purpose

Use the controller to recheck source seals, symbolic-execution freshness, the full Rocq check, manual routes, the three active libraries, forbidden lemmas, and by-product cleanup. The run finishes only after every item passes.

## Required reading

- [Final-apply and final-check flow](workflows/final-check.md)
- [Paths and commands](../verification-orchestrator/workflows/paths-and-commands.md)
- [Controller public interface](../verification-orchestrator/docs/controller-cli.md)

Main does not need to read a group-worker or other subagent skill. The controller mechanically checks forbidden lemmas, proof structure, and source seals. Main only executes the complete invocation carried by the action.
