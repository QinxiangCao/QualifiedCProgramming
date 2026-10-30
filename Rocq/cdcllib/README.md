# CDCLLib: shared semantics for literals, CNFs, SAT and CDCL

This is for readers of the verified SAT solvers and for writers of new
verified programs that deal with formulas, CNFs, SAT or CDCL. Paths are
relative to the repository root, and `file:N` means line N of that file.
`sat_shared_lib.v`, `cdcl_shared_lib.v` and `dune` are in `Rocq/cdcllib/`.
Client files are cited by basename: `.v` files are under
`Rocq/examples/Applications_human/<case>/`, and `.c`/`.h` files under
`QCP_examples/Applications_human/<case>/`, with `<case>` = `CDCL`, `minisat`
or `cnf_trans`. Lines marked "Example (MiniSat)", "Example (CDCL)",
"Example (cnf_trans)" or "Example (TwoSAT)" cite a client as evidence for a
rule that is stated generically.

## 1. What CDCLLib is

CDCLLib defines what "satisfiable" means, and it defines it once.

- **Representation-independent.** No separation logic, no C struct, no heap;
  only `Z`, lists and functions (`sat_shared_lib.v:13-26`,
  `cdcl_shared_lib.v:13-22`).
- **Shared by the solvers.** Each client maps its C encoding onto `literal`,
  `clause` and `cnf` and states its verdicts with `models` and `cnf_unsat`,
  so two solvers that say "UNSAT" mean the same thing.
- **Editing it rebuilds both proof chains**: `cdcl_shared_lib`, the CDCL case
  library and the whole MiniSat chain (`sat_shared_lib.v:22-26`,
  `cdcl_shared_lib.v:25-28`).
- **No axioms.** No CDCLLib declaration depends on an axiom; the SAT
  dichotomy `partial_clause_false_or_true` (`sat_shared_lib.v:429`) is proved
  by computation over the finite clause. Section 10 states what the library
  loads and which axioms the case libraries import.

## 2. Files and logical paths

| file | lines | contents |
|---|---|---|
| `sat_shared_lib.v` | 1664 | literals, clauses, CNFs, valuations, satisfaction, SAT/UNSAT, entailment, per-clause counters, negation, assumptions as unit clauses, restriction to `n` variables |
| `cdcl_shared_lib.v` | 512 | the abstract solver state `cdcl_view`, search invariants, learned-clause certificates, two transition relations, the decision-level bound, the watched-literal frontier |
| `dune` | 8 | `(coq.theory (name CDCLLib) (theories ListLib))` and `(include_subdirs qualified)` |

- **Logical root** `CDCLLib`: `-R cdcllib CDCLLib` (`Rocq/_CoqProject:21`,
  `Rocq/Makefile:109`); `-R Rocq/cdcllib CDCLLib` and
  `-R _build/default/Rocq/cdcllib CDCLLib` (root `_CoqProject:21-22`).
- **Build order**: `CDCLLib_FILES = sat_shared_lib.v cdcl_shared_lib.v`
  (`Rocq/Makefile:116-117`). Dependencies: stdlib and ListLib only.
- **Layering**: `cdcl_shared_lib.v:1` re-exports `sat_shared_lib`:

```coq
From CDCLLib Require Export cdcl_shared_lib.   (* SAT + CDCL vocabulary *)
From CDCLLib Require Import sat_shared_lib.    (* SAT vocabulary only *)
```

The scopes `Z_scope` and `list` are opened `Local`, and ListLib is imported,
not exported: a client opens its scopes and imports ListLib (`Znth`,
`Zlength`) itself. There is no `Section` or `Module`, so names are
`CDCLLib.sat_shared_lib.<name>` / `CDCLLib.cdcl_shared_lib.<name>`.

Example (CDCL, MiniSat): `CDCL_qcp_lib.v:10` and `solver_qcp_model.v:15`
both start with `From CDCLLib Require Export cdcl_shared_lib.`

## 3. The SAT vocabulary (`sat_shared_lib.v`)

### 3.1 Syntax, valuations, well-formedness

| name | line | definition / meaning |
|---|---|---|
| `literal` | 35 | `Pos (x:Z) \| Neg (x:Z)`, a signed variable |
| `clause` / `cnf` | 40 / 43 | `list literal` / `list clause` |
| `valuation` | 46 | `Z -> bool`: a model, i.e. a total assignment |
| `partial_valuation` | 53 | `Z -> option bool`: solver state; `None` = unassigned |
| `sat_function_update` | 61 | point update of any `Z -> A`; every one-variable state change |
| `var_in_range n x` | 87 | `0 <= x < n`: variables are **0-based** |
| `literal_var l` / `literal_wf n l` | 90 / 94 | the variable / it is in range |
| `cnf_wf n F` | 99 | `0 <= n` and every literal of `F` is in range |
| `bounded_valuation n rho` | 104 | `rho` is false outside `[0,n)` |
| `eval_literal rho l` | 108 | value under a total valuation |
| `eval_partial_literal sigma l` | 116 | `Some` value, or `None` if unassigned |

There is no `clause_wf` (use `Forall (literal_wf n)`) and no general formula
type (section 7).

### 3.2 Satisfaction, verdicts, assumptions

| name | line | definition | use it when |
|---|---|---|---|
| `clause_satisfied rho c` | 130 | some literal of `c` is true | one clause; the empty clause is never satisfied |
| `models rho F` | 134 | `Forall (clause_satisfied rho) F` | you have a concrete valuation, for example the solver's model |
| `cnf_sat n F` | 138 | `cnf_wf n F` and some *bounded* `J` with `models J F` | you state SAT without naming the model |
| `cnf_unsat n F` | 148 | `cnf_wf n F` and no *bounded* `rho` models `F` | the UNSAT verdict |
| `entails_clause F c` | 144 | every model of `F` satisfies `c` | soundness of a learned or derived clause |
| `unit_clause l` | 1386 | `[l]` | one assumed literal |
| `cnf_with_units F A` | 1389 | `F ++ map unit_clause A` | a query under assumptions `A`; UNSAT is stated for this formula |

Both verdicts quantify over **bounded** valuations only. This loses nothing:
two valuations that agree on `[0,n)` model the same well-formed CNF
(`models_congr_on_range`, 1579), so any model can be cut down with
`rho_restrict` (1595). A model of `cnf_with_units F A` is a model of `F`
that makes every literal of `A` true (`models_cnf_with_units`, 1526).

### 3.3 Counting vocabulary

These summarise a clause under a partial valuation. A solver that keeps
per-clause counters in C relates its arrays to them.

| name | line | counts / means |
|---|---|---|
| `clause_true_count sigma c` | 159 | literals of `c` that are `Some true` |
| `clause_unassigned_count sigma c` | 171 | literals of `c` that are `None` |
| `clause_false sigma c` | 183 | every literal is `Some false` (a conflict) |
| `clause_unit sigma c` | 189 | true count 0 and unassigned count 1 |
| `literal_var_count x c` | 195 | literals on `x`, either sign |
| `literal_true_at_count x b c` | 206 | literals on `x` made true by `x = b` |
| `clear_partial sigma x` | 219 | unassign `x` (backtracking) |
| `satisfying_literal x b` / `falsified_literal x b` | 224 / 228 | the literal on `x` that `x = b` makes true / false |
| `literal_neg l` | 1323 | flip the sign |
| `clause_var_injective c` | 1243 | two literals of `c` with the same variable are equal; the same literal may occur twice |

`clause_unit` is defined by the counters, not by the literals. A clause that
contains the same unassigned literal twice has unassigned count 2, so it is
not unit. The literal-level characterisation therefore needs `NoDup`
(`clause_counts_unique_none`, 1077).

Use the counters when the C code keeps counts. Use `clause_false` and
`eval_partial_literal` when it does not. Do not define a third notion of
"conflict" or "unit". Example (CDCL): the C state keeps the true and
unassigned counts per clause, and the case relates them to
`clause_true_count` and `clause_unassigned_count`. Example (MiniSat): the C
state keeps no counts, and conflicts are stated with `clause_false`.

## 4. The CDCL vocabulary (`cdcl_shared_lib.v`)

### 4.1 The view

`cdcl_view` (39-46) is the solver state without its C representation. A
client defines one function from its C state to it and states every
contract over that view.

| field | type | meaning |
|---|---|---|
| `assignment` | `partial_valuation` | current assignment |
| `level_of` | `Z -> option Z` | decision level of each variable |
| `reason_of` | `Z -> option clause` | antecedent clause, as a **value**, not an index |
| `assignment_rank` | `Z -> option nat` | position on the trail; a well-founded order |
| `installed_clauses` | `list clause` | the clause database |
| `current_level` | `Z` | current decision level |

### 4.2 Justification and invariants

| name | line | says |
|---|---|---|
| `reason_valid a x c` | 52 | `c` contains `satisfying_literal x b`, and every literal of `c` on another variable is false, at a level `<=` and a rank `<` those of `x`. Database membership is **not** included. |
| `reason_dependency a x y` | 68 | the reason of `x` has a false literal on `y <> x` (an edge of the implication graph) |
| `grounded_at a` | 77 | every assigned variable has a level and a rank, and either no reason or a valid one. Nothing is said about unassigned variables. |
| `decision_at a x d` | 90 | `x` is assigned at level `d` with no reason |
| `closed_levels a` | 98 | `0 <= current_level`, assigned levels lie in `[0, current_level]`, and every level in `(0, current_level]` has a decision. Existence only. |
| `stable_view a` | 121 | `grounded_at a /\ closed_levels a` |
| `restrict_to_level a k` | 107 | the assignment after backjumping to `k` |

The shared invariants are deliberately weak. A solver that maintains more
(unique decisions, reasons in the database) states the shared predicate
conjoined with named local conditions. See section 9, rule A3.

### 4.3 Database facts and certificates

| name | line | says | use it for |
|---|---|---|---|
| `no_conflict a` / `no_unit a` | 153 / 158 | no installed clause is false / unit | propagation has finished |
| `database_conflict a` | 163 | some installed clause is false | a conflict was found |
| `reasons_entailed F a` | 170 | every reason is entailed by `F` | resolving on reasons is sound |
| `db_entailed F a` | 175 | every installed clause is entailed by `F` | learned clauses are sound |
| `reasons_var_injective a` | 180 | every reason is `clause_var_injective` | a variable in a reason determines its literal (`clause_var_injective_var_lit`, `sat_shared_lib.v:1265`); the counting lemmas take `NoDup` separately |
| `learned_clause_sound F a L` | 126 | `entails_clause F L` and `L` is false now | the base of every learning certificate |
| `uip_exit_cert F a L` | 133 | learned-sound, distinct variables, `L = l :: rest` with `l` the only literal at the current level | first-UIP analysis output |
| `clause_asserting_after a target L` | 147 | `L` is unit after `restrict_to_level a target` | a backjump-target certificate |

### 4.4 Transitions and the level bound

| name | line | the abstract effect of |
|---|---|---|
| `assigns_one old new x b d reason` | 187 | enqueue or decide: `x` goes from unassigned to `Some b` at level `d`; its rank exceeds every dependency's; all other variables and the database are unchanged. `current_level` is left to the client, and `reason_valid` is a separate hypothesis. |
| `restrict_above_level old new target` | 208 | backjump: `current_level new = target`; variables at level `<= target` keep all four fields; all others become `None`; the database is unchanged |

No preservation lemma for these transitions is shared; each client proves
its own. `stable_search_level_bound` (238): if `0 <= n`, every assigned
variable is in `[0,n)` and `closed_levels a`, then `current_level a <= n`;
use it to bound a level counter or a trail-limit array. Example (CDCL):
`stable_search_level_bound__solver_analysis_and_returns`
(`CDCL_qcp_lib.v:12707`).

### 4.5 Watched-literal frontier

The theory is generic over an owner type (for example a clause pointer).
`P : literal -> Prop` is the set of processed (true) trail literals;
`P (literal_neg w)` means `w` is false and the clauses watching `w` have been
visited.

| name | line | role |
|---|---|---|
| `watch_occurrence Owner` | 314 | record: owner, body, left and right watch |
| `watch_occurrence_wf n o` | 334 | body literals in range; both watches in the body |
| `watch_frontier occs P` | 342 | no occurrence has both watches processed-false |
| `watch_frontier_except occs P focus` | 351 | the same, except through `focus` (during a scan) |
| `processed_false_complete n rho P` | 394 | every in-range literal false under `rho` has its negation processed (the queue is drained) |
| `watch_frontier_open` / `_close` | 404 / 435 | start / end the scan of one watch list |
| `watch_frontier_shrink` / `_thin` | 362 / 379 | `P` shrinks (backtrack) / occurrences are removed (clause deletion) |
| `watch_frontier_rollback` | 459 | conflict in mid-scan, then backjump |
| `watch_frontier_total_satisfies` | 485 | frontier plus drained queue under a total `rho`: every body is satisfied (the SAT answer) |

Example (MiniSat): `minisat_watch_frontier` (`solver_qcp_model.v:774`)
instantiates `watch_frontier`, and `minisat_watch_fixpoint_sat`
(`solver_qcp_lib.v:2665`) turns `watch_frontier_total_satisfies` into
"every database clause is satisfied by the model".

## 5. Connecting a C encoding: the bridge pattern

Every client has its own C encoding. A bridge maps it onto the library's
types. It is the legitimate place for case-specific definitions.

| layer | (a) reuse unchanged | (b) case-specific adaptation |
|---|---|---|
| literal | `literal`, `literal_var`, `literal_neg`, `eval_*` | one decoder from the C word to `literal`, plus one lemma per C primitive (negate, variable, sign) |
| clause | `clause`, `cnf`, counters | one decoder from the C row or word list to `clause` |
| assignment | `partial_valuation`, `valuation` | one function from the C value array to each |
| solver state | `cdcl_view` and its predicates | one view function from the C state to `cdcl_view` |
| invariant | the shared predicate | the shared predicate `/\` named local conditions |
| database | `entails_clause`, `models` | the relation tying C rows to the input `F` |

Rules:

1. **One decoder per encoding**; every other case predicate goes through it.
2. **State the offsets.** If C variables start at 1 or `0` is padding, the
   decoder drops the padding and shifts to `0 <= x < n`.
3. **One lemma per C primitive** (it commutes with the decoder), then reason
   in library terms.
4. **Resolve indices at the producer.** If C stores a clause index where the
   view has a clause value, convert once and define the index form through
   the shared relation.

Example (MiniSat), packed `2v + sign` literals (`solver_qcp_model.v:60-81`;
`lit_neg_c` is C's `l ^ 1`):

```coq
Definition lit_denote (l : Z) : literal :=
  if Z.odd l then Neg (l / 2) else Pos (l / 2).

Definition lits_denote : list Z -> clause := map lit_denote.
...
Definition lit_neg_c (l : Z) : Z := Z.lxor l 1.
```

Primitive lemmas: `lit_denote_neg`, `lit_var_c_denote`, `lit_denote_wf`,
`lit_true_iff` / `lit_false_iff` (`solver_qcp_lib.v:241, 251, 257, 374, 392`).
Value cells: 1 / -1 / 0 = true / false / unassigned (`lbool_val`,
`solver_qcp_model.v:77-78`). View: `view_of` (393), `msolver_view`
(1951-1952). The invariant record `msolver_inv_weak` (2032) holds
`cnf_wf n F`, `stable_view`, `reasons_entailed` and `reasons_var_injective`
directly as fields.

Example (CDCL), dense rows: a clause is an `int` row of length `n`; 1 means
`x`, -1 means `¬x`, 0 means absent (`CDCL_qcp.h:23`). Decoder: `dense_decode`
(`CDCL_qcp_lib.v:66-77`). Value cells: -1 / 0 / 1 = unassigned / false / true
(`decode_value_cell`, 346), a different code from MiniSat's. View:
`cdcl_view_of_snapshot` (378), with installed clauses
`map dense_decode (snap_rows snap)`. C reasons are row indices (-1 = none).
The transition form resolves them through `reason_clause_of_index` (35-37):

```coq
Definition assigns_one_idx
    (old new : cdcl_view) (x : Z) (b : bool) (d reason : Z) : Prop :=
  assigns_one old new x b d (reason_clause_of_index new reason).  (* :52-54 *)
```

The view's `reason_of` field is `snapshot_reason` (367-376), which repeats
the same resolution over `map dense_decode (snap_rows snap)`. The two agree
because that list is the view's `installed_clauses` (385). Under rule 4, a
new client defines the view's reason field through its one resolver.

Rows are tied to the input by `original_prefix_exact` (79) and
`installed_clauses_sound` (103): the first `|F|` decoded rows are exactly
`F`, and later rows are entailed by `F`. A dense row cannot hold a tautology
`{x, ¬x}` or a repeated literal, and `original_prefix_exact` requires
non-empty input clauses (83), so a front end must deduplicate first and
handle the empty clause itself.

## 6. Stating top-level results

State a verdict about the **original input** `F`, with library names only.

| result | Ensure shape |
|---|---|
| SAT, model returned | `models rho F` for the returned valuation `rho`, under `cnf_wf n F` in the Require or the invariant |
| SAT, model not named | `cnf_sat n F` |
| UNSAT | `cnf_unsat n F` |
| UNSAT under assumptions `A` | `cnf_unsat n (cnf_with_units F A)` |
| SAT under assumptions | `models rho (cnf_with_units F A)`: `rho` models `F` and makes every literal of `A` true (`models_cnf_with_units`) |
| clause added, formula kept | model equivalence: `forall rho, models rho F' <-> models rho (F ++ [c])` |
| resource limit | a separate return code with no verdict |

Neither client uses `cnf_sat`; both name the model. That is a choice of
presentation, not a gap. `models` looks only at in-range variables of a
well-formed CNF. To export `cnf_sat` from a named model, apply
`rho_restrict_bounded` and `models_rho_restrict` (section 8).

Example (CDCL): `cdcl_solver` (`CDCL_qcp.c:835-853`) requires
`cnf_wf(n, F)` and ensures `models(J, F)` on return 1 (843),
`cnf_unsat(n, F)` on return 0 (847), and no verdict on -2 (850). The model is
`rho_of_values` (`CDCL_qcp_lib.v:56`), which is false outside `[0,n)`, so it
is already bounded.

Example (MiniSat), in `solver_qcp.h`: `solver_solve_spec` ensures
`models(rho_of_model(...), F)` with `assumptions_true_under(..., A_arr)` on
1, and `cnf_unsat(n, cnf_with_units(F, A_arr))` on 0. This is the split form
of the SAT-under-assumptions row; it needs the named helper
`assumptions_true_under` (section 9, A6).
`solver_addclause_incremental_spec` gives model equivalence on 1 and
`cnf_unsat(Z::max(n, input_bound), cnf_add_clause(F, input))` on 0;
`solver_simplify_incremental_spec` gives `cnf_unsat(n, F)` on 0.
`rho_of_model` (`solver_qcp_lib.v:2473`) is `Znth x assigns 0 =? 1`. It is
false for `x >= Zlength assigns`, but `Znth` reads cell 0 at a negative
index (`Rocq/listlib/Base/Positional.v:10-11`), so it is **not** bounded
below 0, and a `cnf_sat` form would need `rho_restrict`.

## 7. Formulas and CNF transformation

**What exists.** The only shared propositional syntax is CNF. CDCLLib has no
general formula type, formula evaluation, Tseitin transformation or
equisatisfiability lemma, and no other library under `Rocq/` has a formula
type over `valuation` (`Rocq/unifysl` has deep embeddings with `Prop`-valued
models for the logic generator, not a SAT library).

**What to do in a new case.**

1. Keep the CNF side in CDCLLib terms: decode the output to `cnf` and state
   results with `models`, `cnf_sat` and `cnf_unsat`.
2. Put a general formula type and its evaluation in the case library, for
   now. Evaluate into the shared `valuation`, so formula and CNF share
   models. Keep syntax and evaluation free of separation logic; the heap
   layout is a separate predicate.
3. State what the transformation means, not how it runs: equisatisfiability
   (for example `(exists rho, eval rho phi = true) <-> cnf_sat n G`) or model
   correspondence (models of `G` restrict to models of `phi`, and models of
   `phi` extend to models of `G`). Equating the C result with a Fixpoint
   that replays the algorithm says nothing about satisfiability.
4. Promote the formula type to CDCLLib only when a second client needs it,
   and outside any verification run (section 10).

Example (cnf_trans), what not to copy
(`Rocq/examples/Applications_human/cnf_trans/`):

- `smt_lang_lib.v` puts the formula syntax `smt_prop` (60) in the same file
  as its heap layout `store_SmtProp`, and imports `SimpleC.SL` (11). It has no
  evaluation function.
- `cnf_trans_lib.v` uses `cnf_list`, a parsing-only `Notation` for
  `list (list Z)` (29). Variables are
  nonzero (`SmtV` requires `var <> 0`, `smt_lang_lib.v:87`), `-p` negates,
  and clauses are 0-padded (`[p1; -p3; 0]`). No lemma relates this to
  CDCLLib's `cnf`.
- The `prop2cnf` contract (`cnf_trans.c:306-321`) says only that the C
  result equals `prop2cnf_logic(...)`. That is functional refinement against
  a mirror of the algorithm, not a semantic statement.

A new case of this kind would decode `list (list Z)` to `cnf` (drop `0`, map
`v > 0` to `Pos (v-1)` and `-v` to `Neg (v-1)`) and state equisatisfiability.

## 8. Proof-writing guide

Name the library lemma; do not re-prove it. Lines are in `sat_shared_lib.v`
unless `cdcl:` is given.

| task | lemmas |
|---|---|
| read an updated point | `sat_function_update_eq` (66), `sat_function_update_neq` (74; hypothesis `x <> y`, updated point first) |
| conflict from counters, and back | `clause_counts_zero_false` (692), `clause_false_counts` (392) |
| unit clause: other literals are false | `clause_unit_other_false` (815) |
| unit clause from literals | `clause_counts_unique_none` (1077; needs `NoDup`) |
| not unit: two unassigned literals | `clause_unassigned_count_two_none` (749; no `NoDup`) |
| counters after assign / backtrack | `clause_counts_assign` (529), `clause_counts_clear` (582), `literal_true_at_count_le_true_count` (1024) |
| counters after propagating a unit | `unit_assignment_counts` (922) |
| an unrelated update leaves a literal alone | `eval_partial_literal_other` (1279); `eval_partial_literal_assignment_at` (1291) needs agreement only at the literal's variable |
| negation | `literal_neg_involutive` (1330), `literal_var_neg` (1334), `eval_literal_neg` (1338), `eval_partial_literal_neg` (1347), `literal_neg_satisfying` (1357) |
| read a false literal back as an assignment | `eval_partial_false_shape` (1364) |
| learned clause is sound | `entails_clause_in` (1420), `entails_clause_mono` (1439), `entails_clause_perm` (1412), `entails_unit_step` (1468) |
| assumptions | `models_cnf_with_units` (1526), `models_units_iff` (1485), `entails_clause_units_weaken` (1536), `entails_clause_units_unit` (1546), `entails_units_mono` (1458), `cnf_with_units_wf` (1556) |
| UNSAT | `entails_empty_cnf_unsat` (411): `cnf_wf n F -> entails_clause F nil -> cnf_unsat n F` |
| UNSAT with more assumptions | `cnf_unsat_units_mono` (1629) |
| SAT from a full partial assignment | `partial_clause_false_or_true` (429), `partial_clause_has_true` (458), `eval_partial_literal_total_agree` (474) |
| bounded witness for `cnf_sat` | `rho_restrict_bounded` (1609), `models_rho_restrict` (1618), `models_congr_on_range` (1579) |
| decision depth | cdcl: `stable_search_level_bound` (238) |
| watch lists | cdcl: `watch_frontier_open` / `_close` / `_shrink` / `_thin` / `_rollback` / `_total_satisfies` (404 / 435 / 362 / 379 / 460 / 486) |
| case splits | `literal_eq_dec` (237, transparent); `clause_mem_dec` (241) and `clause_var_occurs_dec` (255) are `Qed`, so they do not compute |
| list positions | `Znth_In` (288, arguments `l d i`), `Forall_Znth_elim` (274), `znth_out_of_bounds` (378) |

Proving `cnf_sat n F` from `cnf_wf n F` and `models rho F`:

```coq
split; [exact Hwf |].
exists (rho_restrict n rho).
split; [apply rho_restrict_bounded | apply models_rho_restrict; assumption].
```

Routes. **UNSAT**: a clause false at level 0 entails the empty clause, then
`entails_empty_cnf_unsat`. **SAT**: a total, conflict-free assignment gives
each clause a true literal (`partial_clause_has_true`), carried to the model
by `eval_partial_literal_total_agree`. Example (CDCL):
`root_conflict_implies_cnf_unsat__solver_analysis_and_returns` (12657) and
`model_ready_models_original__solver_analysis_and_returns` (12411) in
`CDCL_qcp_lib.v`.

A `shared /\ local` invariant (rule A3) gives the shared predicate by
`proj1`. Example (CDCL): `grounded_at_cdcl_elim` / `_intro`
(`CDCL_qcp_lib.v:180` / `205`) and the tactic `cdcl_shape` (266).

If a lemma is missing, prove it in the case library under its own name and
record the gap; do not edit CDCLLib during a verification run.

## 9. Anti-patterns

| # | anti-pattern | do instead |
|---|---|---|
| A1 | redefining `literal`, `clause`, `cnf`, `valuation`, satisfaction or unsatisfiability in a case | import CDCLLib; write a decoder |
| A2 | a case-named or group-suffixed copy of a library lemma | name the library lemma |
| A3 | a second, near-identical copy of a shared invariant; or adopting the weaker shared one and silently proving less | `shared /\ named local conditions` |
| A4 | a top-level verdict stated with a case-local notion (a predicate over C arrays, a private `satisfiable`) | `models`, `cnf_sat`, `cnf_unsat`, `cnf_with_units` on the input `F` |
| A5 | an `Extern Coq` signature that differs from the library type | copy the type from the `.v` file |
| A6 | restating the body of a shared definition | use the shared name |
| A7 | a transformation spec that only mirrors the algorithm | a semantic relation (section 7) |
| A8 | a clause index where the view expects a clause value, used in many places | resolve once at the producer (section 5, rule 4) |

Example (MiniSat), A6: `assumptions_true_under`
(`solver_qcp_lib.v`) restates the right-hand side of
`models_units_iff`. A restated name is defensible only where an annotation
needs it, since annotations cannot write a lambda (compare `model_is_total`).

## 10. Trust boundary and known limits

**Trust boundary.**

- **CDCLLib.** Neither file has an `Axiom`, `Parameter` or `Admitted`, and
  no CDCLLib declaration depends on an axiom. Its
  imports are the stdlib and ListLib. `sat_shared_lib.v:8` imports
  `ListLib.General.NoDup`, which does `Require Import Coq.Logic.Classical`
  (`Rocq/listlib/General/NoDup.v:2`), so loading CDCLLib loads the axiom
  `classic`; no CDCLLib declaration uses it.
- **Case libraries.** Both case libraries use the axiom `functional_extensionality`
  (`Coq.Logic.FunctionalExtensionality`) to prove equalities between
  functions, such as a `cdcl_view` field after a transition (section 4.1).
  Example (CDCL): imported at `CDCL_qcp_lib.v:7`, for example in
  `restrict_current_eq_assignment__bcp_unit_to_assignment`. Example (MiniSat):
  imported by `solver_qcp_model.v`, `solver_qcp_tactics.v`,
  `solver_qcp_model_tactics.v` and `solver_qcp_lib.v`, for example in
  `view_of_push_assignment` (`solver_qcp_lib.v`). The clients also load the
  separation-logic framework, whose `AUXLib.Axioms` imports
  `FunctionalExtensionality` and `PropExtensionality`
  (`Rocq/auxlibs/Axioms.v:1-2`); this section does not list the framework's
  own axioms.
- **Generated files.** Each client's `*_proof_auto.v` is `Admitted` by
  design: it holds the VCs that QCP's automation discharges, and those are
  trusted with the QCP engine. The `Axiom`s in `*_goal.v` are the
  `Module Type VC_Correct` signature that `*_goal_check.v` implements with the
  proofs.

**Run controller.** The controller's fixed load paths map `Rocq/cdcllib` to
`CDCLLib` (`.agents/scripts/vc-proving/coq_tooling_common.py:35`), so a
controller-run case can `From CDCLLib Require`. CDCLLib is not one of the
case's own modules, so a run treats it as a base dependency: the controller's
Make or Dune backend builds it with the rest of the case's dependency closure
("Dependency preparation and Rocq" in
`.agents/skills-en/verification-orchestrator/workflows/paths-and-commands.md`).

**`Assignment`** (50) is `valuation` under the name the CDCL annotations use
(48-49). New clients write `valuation`.

**Weak invariants, no preservation lemmas.** `grounded_at` says nothing
about unassigned variables; `closed_levels` asks only that decisions exist
(rule A3). CDCLLib has no lemma that `assigns_one` or
`restrict_above_level` preserves them; each client proves its own
(section 4.4).

**Missing generic lemmas.** There is no `models` or `clause_satisfied` lemma
over `app`/`cons` (unfold `models`, then `Forall_app`/`Forall_cons`, as
`models_clause_units_intro` does at 1502-1511; `in_app_iff` for
`clause_satisfied`),
and no transitivity lemma for `entails_clause` (only `_in`, `_mono`, `_perm`
and the unit forms at 1433-1567). A client that needs one proves it once
over CDCLLib names and records it as a library gap.

**Generic list lemmas.** `Forall_Znth_elim`, `Znth_In`, `Znth_map`,
`replace_Znth_replace_Znth_Same` and `NoDup_Z_bounded_length` (273-370) do
not depend on CDCLLib. Clients call some of them by qualified name, such as
`sat_shared_lib.Forall_Znth_elim` in `solver_qcp_proof_common.v` and
`solver_qcp_proof_manual_part1.v`, so moving them breaks those callers.

**Editing CDCLLib** rebuilds both proof chains. Make library changes outside
a verification run, as their own change, and rebuild both clients.
