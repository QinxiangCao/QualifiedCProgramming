# Group Commands and Checks

Run only the handoff's exact argv/cwd for coq-debug, group-development, and group-check. Main owns claim/finalize. Workers do not step, retry, merge, or run parent/final actions.

Commands are structured JSON objects with `argv` and `cwd`. Preserve the interpreter, each argument, and their order. Prefer a tool accepting an argument list. If a terminal tool accepts only shell text, quote each argument for the actual shell: POSIX shell quoting on POSIX; PowerShell `&` with single-quoted arguments and doubled embedded apostrophes on PowerShell. Set cwd separately when supported. Continue the same live session until actual exit; success requires exit zero and JSON status passed. Do not change backend/target/flags or invoke raw Coq/Dune/Make/coqdep.

The controller derives copied-file overlays, exact/development directories, wrappers, and the authorized debug script. Staging normalizes source in memory and writes changes once; current modules actually compile each time. Dune/Make refresh base dependencies through the same dependency-plan format. Owners do not select backend, targets, or flags.

Checks protect current statements, declaration order, unassigned spans, unused LLM splits, seed libraries, helper suffix/import boundaries, and forbidden assumptions. Development allows assigned spans to remain Abort. Exact checks require complete assigned witnesses/aggressive splits and the selected proof mode. Group wrappers do not run the global goal-check; parent/final validate the full combination. A case library is compiled even when goal-check does not import it.

Historical proofs/helpers and optional reuse notes are not validation receipts. `finalize-delivery` performs complete acceptance against the latest files: completed requires full structure and group Rocq success; annotation-gap requires exact blocker/VC/location data and safe ownership boundaries, without pretending the unprovable target passed. Report/proof repairs follow the feedback in the same owner and directory.

Subprocesses within each coq-check/coq-debug share a 900-second budget. Timeout/pause terminates the tool and cleans child processes; preserve any incomplete-cleanup diagnostic for main. Paths and file types remain validated; links, junctions, and reparse points cannot bypass the fixed workspace.
