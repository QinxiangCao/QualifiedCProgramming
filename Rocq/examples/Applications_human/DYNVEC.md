# DynVec: growable vectors for verified C

For writers of verified C programs that use growable vectors, and for readers
of proofs that use them. Paths are relative to the repository root. Lemmas,
definitions, strategy rules and C functions are cited by name or rule id. Lines
marked "Example (MiniSat)" cite the MiniSat port that uses the library, as
evidence for a rule stated generically.

## 1. What the library is and why

A C growable vector is `struct { int size; int cap; T *ptr; }`. A naive
specification exposes all three fields. Then every client annotation names the
capacity, and every client VC carries it, although almost no client code cares
about it.

The library is `dynvec_lib.v` (with the list lemmas of `list_index_lib.v`). Its
functor `DynVec` describes one vector and hides the capacity inside the
representation predicate; its functor `VecArray` describes a C array of vector
structs:

- `rep v l` says: the vector at address `v` holds the list `l`. The buffer and
  the capacity exist, but they are not named.
- The vector operations are verified once, in their own C unit, and clients
  call them through its contracts. No vector body is re-verified in a client.
- QCP strategy rules open and close the predicate automatically, so most client
  VCs that touch a vector never mention its fields.

The existing instances are `Veci`, `Vecp` and `VecpArray` in
`Rocq/examples/Applications_human/minisat/vec_qcp_lib.v`. Their C unit is
`vec_qcp.h` / `vec_qcp.c` (`new`, `delete`, `push`, `begin`, `size`, `resize`,
`remove`) with the rules in `vec_qcp.strategies`. A program whose C already
uses `veci` / `vecp` uses these instances (section 6); another struct layout or
element type gets its own instance (section 7).

### Comparison with the LLM_bench vector

The corpus has a second verified vector for the same upstream `vec.h`:
`QCP_examples/LLM_bench/Engineering/minisat/vec.{h,c}` with
`Rocq/examples/LLM_bench/Engineering/minisat/vec_lib.v`. It makes different
choices:

| point | LLM_bench `vec` | DynVec |
|---|---|---|
| definitions | written out per type (`veci_header`, `veci_buffer`, `veci_raw`, `store_veci`, and the `vecp_*` twins) | one functor over an element array and a struct layout (section 2) |
| capacity | `store_veci` hides buffer and capacity, but `veci_push` requires `veci_raw(v, buf, cap, xs)` with the capacity named, plus a growth bound when the vector is full, and returns the new buffer and capacity | `push` is on `rep`: no capacity and no bound at the call; the body stops at `cap == INT_MAX` (section 4) |
| live buffer | `IntArray.full buf (Zlength xs) xs` (`veci_buffer`) | `E.seg p 0 (Zlength l) l` inside `rep_at`, so close rules come in a `seg` and a `full` variant (section 8) |
| allocation | libc `malloc`/`realloc`/`free`, each with case-local specs selected by `where` at the call | trusted typed wrappers in `vec_qcp_runtime.h`; their native forms stop the process on failure (section 10) |
| tables and automation | no table of vectors, no strategy file; bodies open and close the vector with `which implies` | `VecArray` for tables and 62 strategy rules (sections 5 and 8) |

DynVec keeps the capacity out of every client contract and annotation. In a VC
it appears where a strategy rule opens a vector: the rule adds a fresh
existential `cap`, which sits in the `header` it leaves, and the pure facts
`0 <= Zlength l`, `Zlength l <= cap`, `cap <= INT_MAX` and `vec_buf_ok cap p`
(section 8). Example (MiniSat): `order_update_safety_wit_1` binds `cap` and has
`vec_buf_ok cap p`, `cap <= INT_MAX` and `Zlength heap0 <= cap` among its
hypotheses.

## 2. Layers and files

Layering: `dynvec_lib.v` does `Require Export list_index_lib`; `vec_qcp_lib.v`
does `Require Export dynvec_lib`; `vec_qcp_def.h` brings `vec_qcp_lib` into
annotations (its `Import Coq Require Import` line); `vec_qcp.h` includes
`vec_qcp_def.h`; your C file includes `vec_qcp.h`.

| file | role | reuse |
|---|---|---|
| `Rocq/examples/Applications_human/list_index_lib.v` | pure list lemmas, no separation logic | unchanged |
| `Rocq/examples/Applications_human/dynvec_lib.v` | the functors and their lemmas | unchanged |
| `Rocq/examples/Applications_human/minisat/vec_qcp_lib.v` | instances for `veci_t` / `vecp_t` | unchanged if you use `veci`/`vecp`; a pattern to copy otherwise |
| `QCP_examples/Applications_human/minisat/vec_qcp_def.h` | the `Extern Coq` block | unchanged |
| `QCP_examples/Applications_human/minisat/vec_qcp.h` | contracts | unchanged |
| `QCP_examples/Applications_human/minisat/vec_qcp.strategies` | 62 rules | unchanged; mirrored for a new struct |
| `QCP_examples/Applications_human/minisat/vec_qcp.c` | the 14 verified bodies (case `minisat/vec_qcp`) | unchanged |
| `QCP_examples/Applications_human/minisat/vec_qcp_runtime.h` | `vec_int_*` / `vec_ptr_*` allocator contracts, `qcp_assert` | trust boundary (section 10) |

`vec_qcp_runtime.h` is included by `vec_qcp.c`. A client that calls the
runtime names itself includes it from its own boundary header. Example
(MiniSat): `minisat_qcp_compat.h` includes `vec_qcp_runtime.h`.

`vec_qcp_lib.v` says in its header comment that it "depends on nothing of the
solver", and `vec_qcp_def.h` and `vec_qcp.strategies` say the same in their headers. The
`vec_qcp.*` unit sits under `minisat/`, next to the MiniSat port that uses it.
The case-independent abstraction is `dynvec_lib.v` plus `list_index_lib.v`.

### The functors in `dynvec_lib.v`

| module | parameters | gives |
|---|---|---|
| `Module Type VEC_ELEMS` | | element buffer: `A`, `seg`, `undef_seg`, and the obligations `seg_nil_frame`, `undef_seg_nil_frame`, `seg_truncate` |
| `Module Type VEC_LAYOUT` | | `struct_name`, `size_field`, `cap_field`, `ptr_field` (strings) |
| `Module Type ARRAY_VIEW (ES)` | | the members of `ArrayLib ES` that vectors need |
| `Module ArrayElems (ES : ELEMENT_STORE) (AL : ARRAY_VIEW ES)` | a framework array library | a `VEC_ELEMS`, with the three obligations proved |
| `IntElems`, `PtrElems` | | `ArrayElems` over `IntArray` / `PtrArray` |
| `Module DynVec (E : VEC_ELEMS) (L : VEC_LAYOUT)` | | one vector: `shell`, `header`, `rep_at`, `rep_ptr`, `rep`, `slot`, lemmas |
| `Module Type VEC_STORE` | | `A`, `rep`, `slot`, `shell`; any `DynVec` instance matches |
| `Module VecArray (V : VEC_STORE)` | | a C array of vector structs, in the framework array shape |

A hand-written `VEC_ELEMS` instance must prove `seg_nil_frame`,
`undef_seg_nil_frame` and `seg_truncate` itself; `ArrayElems` proves them from
the array library.

The instances in `vec_qcp_lib.v`:

```coq
Module Veci := DynVec IntElems VeciLayout.
Module Vecp := DynVec PtrElems VecpLayout.
Module VecpArray := VecArray Vecp.
```

`VeciLayout` and `VecpLayout` name the structs
`"veci_t"` and `"vecp_t"`, each with the fields `"size"`, `"cap"` and `"ptr"`.
`Vecp` stores pointers as `Z`. There is no `VeciArray`.

Name clash to keep in mind: `VecpArray.seg` / `VecpArray.undef_seg` describe
an array of vector **structs**. `IntElems.seg` / `PtrElems.seg` describe the
**element buffer** inside one vector.

## 3. The views

| predicate | definition | names | use it when |
|---|---|---|---|
| `shell v` | three `|->_` cells (Int, Int, Ptr) | nothing | the struct is uninitialised: before `new`, after `delete` |
| `rep v l` | `EX p cap, rep_at v p l cap` | contents | you only care about contents, or the call may grow the vector (`push`, `remove`). Also the form stored in records |
| `rep_ptr v p l` | `EX cap, rep_at v p l cap` | contents, buffer | code took `begin` and walks or overwrites the buffer without growing it |
| `rep_at v p l cap` | below | contents, buffer, capacity | Rocq lemmas only; it has no C-side declaration |
| `header v p n cap` | the three field cells | length, buffer, capacity | never written by hand; the strategies leave it when they open a vector for a buffer access |

The body of `rep_at`:

```coq
“ 0 <= Zlength l <= cap /\ cap <= INT_MAX /\ vec_buf_ok cap p ” &&
( header v p (Zlength l) cap **
  E.seg p 0 (Zlength l) l ** E.undef_seg p (Zlength l) cap )
```

`header` keeps the three field cells packed. A client VC that reads or writes
the buffer sees `header * seg * undef_seg`, never a raw field cell; only the
vector unit's own bodies, which touch `v->size`, `v->cap` and `v->ptr`, see the
fields.

`vec_buf_ok cap p := cap = 0 -> p = 0`: a vector without
capacity stores `NULL`, so `free` and `realloc` of its buffer are defined.

A client annotation writes `rep` or `rep_ptr`, never `rep_at` or `header`.
MiniSat examples appear in `solver_qcp_analysis.c`,
`solver_qcp_solver_propagate.c`, `solver_qcp_state_search.c` and
`solver_qcp_support.c`.

The `rep_ptr` view in a loop: take the buffer with `begin`, then hold
`rep_ptr(v, buf, l)` in the invariant while the loop reads `buf[j]`.
Example (MiniSat): `veci_begin(&s->tagged)` then `Veci::rep_ptr(&(s->tagged),
tagged, tagged_now)` in the invariant, in `solver_lit_removable`. When a loop
reads the buffer back through a local that holds the result of `begin`, rules
60 and 68 cancel the two segments (section 8).

## 4. The C API of the `Veci` / `Vecp` instances

From `QCP_examples/Applications_human/minisat/vec_qcp.h`. The `vecp_*` functions
have the same contracts with `Vecp::`.

| function | Require | Ensure | view |
|---|---|---|---|
| `veci_new(veci* v)` | `Veci::shell(v)` | `Veci::rep(v, nil)` | shell → rep |
| `veci_delete(veci* v)` | `Veci::rep(v, l)` | `Veci::shell(v)` | rep → shell |
| `veci_begin(veci* v)` | `Veci::rep_ptr(v, p, l)` | `__return == p && Veci::rep_ptr(v, p, l)` | rep_ptr |
| `veci_size(veci* v)` | `Veci::rep_ptr(v, p, l)` | `__return == Zlength(l) && Veci::rep_ptr(v, p, l)` | rep_ptr |
| `veci_resize(veci* v, int k)` | `0 <= k && k <= Zlength(l) && Veci::rep_ptr(v, p, l)` | `Zlength(sublist(0, k, l)) == k && Veci::rep_ptr(v, p, sublist(0, k, l))` | rep_ptr |
| `vec_next_capacity(int cap)` | `0 <= cap <= INT_MAX && emp` | `cap < __return <= INT_MAX` and the growth rule | pure |
| `veci_push(veci *v, int e)` | `Veci::rep(v, l)` | `Veci::rep(v, app(l, cons(e, nil)))` | rep |
| `vecp_remove(vecp* v, void* e)` | `In(e, l) && Vecp::rep(v, l)` | `exists k, first_occurrence(e, l, k) && Vecp::rep(v, remove_nth(k, l))` | rep |

`push` hides growth: its Ensure is `rep`, so no capacity reaches a client.
`new` and `push` Require no length or capacity bound, and a client must not add
one. At `cap == INT_MAX`, `vec_next_capacity` (called by `push` to grow) calls
the trusted `vec_resource_stop` (`Ensure 0 == 1`, in `vec_qcp_runtime.h`), so
that path never returns. A failed allocation never reaches a body: the trusted
allocator contracts promise a normal return with a non-`NULL` buffer (the
header comment of `vec_qcp_runtime.h` and the Ensures of
`vec_int_array_realloc`, `vec_ptr_array_alloc` and `vec_ptr_array_realloc`),
and their native forms stop the process on failure (`vec_checked_alloc`,
`vec_checked_grow`). This is vec_qcp's choice, not a DynVec
requirement (section 7, step 10).
`resize` only truncates and keeps the buffer, so it is on `rep_ptr`.
`first_occurrence` and `remove_nth` are in `list_index_lib.v`;
`first_occurrence_perm` turns `vecp_remove`'s Ensure into a
`Permutation`.

## 5. Arrays of vectors: `VecArray`

`VecArray V` views a C array of vector structs with the framework's generic
`store_array_*` predicates. Each element is one whole vector, `V.rep`.

| predicate | meaning |
|---|---|
| `vec_store x i l` | `V.rep (V.slot x i) l`: slot i holds l |
| `seg x lo hi ls` | slots `lo..hi-1` hold `ls` |
| `full x n ls` | slots `0..n-1` hold `ls` |
| `missing_i x i lo hi ls` | `seg x lo hi ls` with slot `i` taken out |
| `missing2 x i j n ls` | `full x n ls` with slots `i` and `j` taken out; carries `Zlength ls = n` |
| `undef_seg x lo hi` | slots `lo..hi-1` are uninitialised shells (`vec_undef_store x i` is `V.shell (V.slot x i)`) |
| `undef_missing_i x i lo hi` | `undef_seg x lo hi` with slot `i` taken out |
| `undef_full x n` | slots `0..n-1` are uninitialised shells |

`slot base i := base + i * sizeof(L.struct_name)`; rewrite with `slot_eq`.

`VEC_STORE` takes `slot` as a parameter, and `VecArray` never computes with it:
the functor has no `sizeof`, no shift axiom and no alignment premise. So an
implementation can place its vectors in any layout (a padded stride, vectors at
an offset inside a larger record, a non-uniform placement) and every `VecArray`
lemma applies. The framework's `ELEMENT_STORE` fixes a contiguous affine
layout through its shift and alignment axioms. The cost is at the QCP level:
symexec does not know that `slot` is `base + i * sizeof`, so the strategies
handle each spelling of a slot address separately (below).

The "one slot open" shape is `missing_i` plus the open slot's `vec_store`. The
"two slots open" shape is `missing2` plus two `vec_store`s. There is no other
hole predicate.

| step | lemma (`VecpArray.`) |
|---|---|
| take one slot out | `full_split_to_missing_i`, `seg_split_to_missing_i`; stated at the slot's address, `full_split_to_slot` |
| put it back | `missing_i_merge_to_full`, `missing_i_merge_to_seg`; stated at the slot's address, `slot_merge_to_full` |
| take a second slot out while one is open | `missing_i_split_to_missing2` |
| put the second back | `missing2_merge_to_missing_i` |
| take two out of `full` | `full_split_to_missing2` |
| put two back into `full` | `missing2_merge_to_full` |
| facts | `missing_i_Zlength`, `missing_i_index_range`, `seg_Zlength`, `full_Zlength` |
| build segments | `seg_single`, `full_to_seg`, `seg_to_full`, `seg_merge_to_seg`, `seg_split_to_seg`, `seg_unfold`, `missing_i_unfold` |
| segments around an open slot | `missing_i_split_to_seg`, `seg_merge_to_missing_i` |
| empty arrays | `seg_empty`, `full_empty`, `undef_seg_empty`, `undef_full_empty`, `undef_missing_i_empty` |
| uninitialised slots | `undef_seg_unfold`, `undef_missing_i_unfold`, `undef_full_to_undef_seg`, `undef_seg_valid` |

`seg_to_full` takes a segment that starts at slot 0 only. ArrayLib's
`seg_to_full` moves the base to element `lo`, which needs the address
arithmetic that `slot` keeps abstract (the comment above `seg_to_full` in
`dynvec_lib.v`).

The merge lemmas produce `replace_Znth i a ls`. The list facts that go with
them are in `list_index_lib.v`: `replace_Znth_split`,
`sublist_replace_Znth_outside`, `replace_Znth_comm`.

The Externs in `vec_qcp_def.h` export `VecpArray::full`, `missing_i`,
`missing2` and `undef_seg`. `full x m ls` implies `Zlength ls = m`
(`full_Zlength`), so a client name for a whole table needs no length conjunct
for soundness. Carry one when the rules that open the name should hand the
length to symexec as a pure fact. Example (MiniSat): `wlists_rep` carries
`Zlength wm = 2 * n` (`solver_qcp_model.v`), and client rules 93/94,
which open `wlists_rep` for the table rules, add that conjunct to the
precondition next to `VecpArray::full`.

Two slots touched one after the other need no `missing2`: open the first,
operate, merge it back into the updated list, then open the second of that
list. This also covers equal indices; the `missing2` lemmas
(`missing_i_split_to_missing2`, `missing2_merge_to_missing_i`,
`full_split_to_missing2`, `missing2_merge_to_full`) require `i <> j`.

### Strategy rules for a table

Rules 401-409 and 411-416 of `vec_qcp.strategies` (`VecpArray` only) take one slot out of
a `VecpArray::full` and put it back. A slot `i` of a table at `b` reaches them
in three spellings:

- `Vecp::slot(b, i)`;
- an alias `w` with `w == Vecp::slot(b, i)` in the context, as returned by an
  accessor whose Ensure is `__return == Vecp::slot(base, k)`;
- the C address `&b[i]`, which the frontend writes
  `pointer_offset(b, i, struct vecp_t)`; it equals `Vecp::slot(b, i)` by
  `slot_eq`.

| ids (slot / alias / C address) | priority | effect |
|---|---|---|
| 401 / 403 / 405 | core(1) | `full(b, n, ls)` on the left, `Vecp::rep` of slot `i` on the right: leave `missing_i(b, i, 0, n, ls)` and ask `l == Znth(i, ls, nil)`; checks `0 <= i < n` |
| 402 / 404 / 406 | core(1) | `full` on the left, `rep_ptr` or a field of slot `i` on the right: take the slot out as `Vecp::rep` under the same spelling, for the vector rules to open |
| 407 | core(1) | `full` on the left, `missing_i(b, i, 0, n, ms)` on the right: take slot `i` out and ask `ms == ls` |
| 408, 409 | core(1) | two `full`s, or two `missing_i`s, at one base with provably equal bounds: ask the contents equal |
| 411 / 413 / 415 | post(1) | `missing_i(b, i, 0, n, ls)` and slot `i` back with `Znth(i, ls, nil)`: refold to `full(b, n, ls)` |
| 412 / 414 / 416 | post(3) | the same with any contents `l`: refold to `full(b, n, replace_Znth(i, l, ls))` |

With these rules, a call on one slot of a table held as `VecpArray::full`
needs no annotation. Example (MiniSat): `clause_remove` calls `vecp_remove` on
two watch lists through `solver_read_wlist` with no
annotation around the calls; the table rules take each slot out and refold
the table.

What needs annotations or proof steps:

- two slots out at once: the rules never produce `missing2`;
- a slot held open across a loop: the invariant states `missing_i` and the
  slot's view;
- a segment, or a `missing_i` that does not start at slot 0 (the take-out and
  refold rules 401-407 and 411-416 need slot 0; rule 409 matches two
  `missing_i` at one base with provably equal slot and bounds, at any slot);
- uninitialised slots (`undef_seg`) and growing the table (section 9);
- a client's own name for the table: open it with client rules and close it
  with a lemma. Example (MiniSat): rules 93/94 open `wlists_rep`;
  `full_to_wlists_rep` and `missing_i_merge_to_wlists_rep` close it.

Without a table on the left (for example a slot already handed out by a
`missing2` split), rules 116 and 95 relate an alias to `Vecp::slot`: 116
matches a `rep` held under the alias, 95 closes a slot opened under the alias
from its `header`. No rule outside 405/406/415/416 relates a raw C address to
`slot`; spell such a slot with the call's own lvalue in a `which implies` and
relate it to `slot` with `slot_eq` in the proof.
Example (MiniSat): the accessor `solver_read_wlist`, called in `clause_new`,
`clause_remove` and `solver_propagate`; the lvalue spelling
`Vecp::shell(&(s->wlists[2*var]))` before `vecp_new` on an uninitialised slot,
in `solver_setnvars`.

## 6. Using the library from a new case

### If your C uses `veci` / `vecp` unchanged

1. `#include "vec_qcp.h"` in your C file. It includes `vec_qcp_def.h`
   and the strategy file through
   `/*@ include strategies "vec_qcp.strategies" */`. This
   brings all 62 vector rules, including the table rules 401-409 and 411-416 and the
   segment rules 60/68 (section 8).
2. Keep exactly one `vec_qcp.h` under `QCP_examples`. The controller's symexec
   wrapper resolves a quoted include in this order: the including file's own
   directory, then the collection directory (`QCP_examples/<collection>/`) and
   the strategy profile, then known include directories, and only then a
   repository-wide path-tail search, which fails on more than one match
   (`_resolve_include` in `.agents/scripts/verification-orchestrator/symexec_tooling.py`).
   So a copy next to your C file is picked first and silently forks the
   contracts, and a copy elsewhere makes the fallback search ambiguous.
3. The generated goal then imports `vec_qcp_lib`, `vec_qcp_strategy_goal` and
   `vec_qcp_strategy_proof`, and its `VC_Correct` includes
   `vec_qcp_Strategy_Correct`, as in the vector unit's own goal
   `Rocq/examples/Applications_human/minisat/vec_qcp_goal.v`.
   Example (MiniSat): `solver_qcp_goal.v`.
4. Your goal_check must therefore include the vector strategy proof next to
   your own: `Include vec_qcp_strategy_proof.`, as `vec_qcp_goal_check.v` does.
   Example (MiniSat): `solver_qcp_goal_check.v`.
5. Build the vector `.vo` files with `make all`, `make examples` or
   `make examples-applications` in `Rocq/`. They are in `APPLICATION_Lib_FILES`
   and `APPLICATION_STRATEGY_FILE_NAME` in `Rocq/Makefile`, but **not** in
   `CORE_EXAMPLE`. The default `make` (target `core`) does not build them. The
   same targets build the vector unit's own case `minisat/vec_qcp` (in
   `APPLICATION_FILE_NAME`), which verifies the 14 bodies; your case verifies
   only your functions, and vector calls use the contracts.

The Coq load path is `-R examples SimpleC.EE` (`COQ_FLAG` in `Rocq/Makefile`). Every
`Open Scope` in `list_index_lib.v`, `dynvec_lib.v` and `vec_qcp_lib.v` is
`Local`, and they define no notations. `SeparationLogic` and `ListLib` are
imported, not exported, by these files; the generated goal files import them
themselves.

### Header and definition contracts

QCP binds a function to the last contract it reads, so the header and the
definition must carry identical contracts. Nothing checks this mechanically:
after any contract edit, compare the two copies.

## 7. Adapting to another struct layout or element type

### Decision: does DynVec fit your struct?

`shell`, `header`, every intro lemma and every strategy fix the field types:
size and capacity are `Int` / `I32`, the buffer field is `Ptr` / `PTR`, and the
bounds are `INT_MAX`. `rep_distinct` also reads
the size field as an `int` cell (`dup_store_int`). Field names are free (they
come from `VEC_LAYOUT`), and fields are addressed by name, so their order is
free.

The struct must have exactly these three fields. `shell` and `header` own
exactly three cells, and step 4 defines QCP's uninitialised-struct predicate
as `MyVec.shell`; for a struct with a fourth field that predicate covers four
cells, so the definition and its rules would drop one.

If the struct is exactly `int`, `int`, pointer, use DynVec. If size or capacity
is not `int` (e.g. `size_t`, `unsigned`), the buffer is not a pointer field, or
the struct has more fields, stop: DynVec does not apply as is. Extend the
library (field types or extra fields as layout parameters, new rules) rather
than hand-rolling a predicate in the client. A pointer triple (`begin`, `end`,
`cap_end`) is such a layout: size and capacity are pointer differences, so a
sibling functor would have to derive them (`end - begin` is a `long` divided
by the element size; check QCP's pointer-difference support with symexec). The
alternative is a C change to `int` size and capacity fields.

The strategies also match `veci_t` / `vecp_t`, the field names and
`IntArray::` / `PtrArray::` literally, so a new struct needs its own rules:

1. Layout:
   ```coq
   Module MyLayout <: VEC_LAYOUT.
     Definition struct_name := "my_t". Definition size_field := "len".
     Definition cap_field := "room".   Definition ptr_field := "data".
   End MyLayout.
   ```
2. Elements: `IntElems` or `PtrElems` for int or pointer elements. Otherwise
   `Module MyElems := ArrayElems Store<T>AsElement <T>Array.` with a pair from
   `Rocq/SeparationLogic/ArrayLib.v` (for example `CharArray`, `UIntArray`,
   `UInt64Array`, `DoubleArray`). The repository
   instantiates only `IntArray` and `PtrArray`.
3. `Module MyVec := DynVec MyElems MyLayout.` and, for a table of vectors,
   `Module MyVecArray := VecArray MyVec.`
4. `Definition UndefStructPredmy_t (v : Z) : Assertion := MyVec.shell v.`
   (pattern: `UndefStructPredveci_t` in `vec_qcp_lib.v`). QCP uses this name
   for an uninitialised local struct (rules 9/10 and 109/110).
5. A def header with `Import Coq Require Import <your lib>` and an Extern block
   for `vec_buf_ok`, `MyVec::shell/rep/rep_ptr/header` and
   `UndefStructPredmy_t`, plus `MyVec::slot` and
   `MyVecArray::full/missing_i/missing2/undef_seg` for tables (pattern:
   `vec_qcp_def.h`). Every mirrored open and close rule uses
   `vec_buf_ok`; the strategy file sees it only through this header.
6. A strategy file that starts with `#include` of that def header (pattern:
   the top of `vec_qcp.strategies`) and mirrors the 21 `Veci` rules (ids 2, 5, 7-10,
   70, 201-203, 205-215) with your struct, field names, C element type and
   array library. Mirror the `Vecp` extras 116 and 95 (slot aliases) and 35
   (resize re-close), the table rules 401-409 and 411-416 and the segment rules 60/68 only
   if you need them.
7. In your C header, `/*@ include strategies "<your file>.strategies" */`
   (pattern: `vec_qcp.h`).
8. Strategy proofs: copy `Rocq/examples/Applications_human/minisat/vec_qcp_strategy_proof.v`
   with the module and the imports of `vec_qcp_strategy_goal` and
   `vec_qcp_lib` renamed,
   and the framework calls `IntArray.full_to_seg`, `IntArray.seg_to_full` and
   their `PtrArray` twins replaced by your element array's. The proofs unfold
   no vector predicate: they apply `header_fold`/`header_open`,
   `shell_fold`/`shell_open`, `rep_open`/`rep_ptr_open`/`rep_at_open`, the
   intro lemmas, the bounds lemmas, the conversions between views and, for
   table rules, `full_split_to_slot`, `slot_merge_to_full` and
   `missing_i_index_range`, with generic tactics (`LLM_pre_process`,
   `int_auto`).
9. Build registration in `Rocq/Makefile`: the lib in `APPLICATION_Lib_FILES`,
   the strategy file in `APPLICATION_STRATEGY_FILE_NAME`, and the vector
   unit's own case in `APPLICATION_FILE_NAME`.
10. The C operations, verified in their own unit, with identical contracts in
    the header and the definition.
    Contracts state the same views as `vec_qcp.h` (`shell` → `rep v nil`,
    `rep v l` → `rep v (l ++ [x])`, ...). The bodies are the implementation's
    own code: `rep` hides the capacity, so any growth policy (`cap + 8`,
    doubling, a separate `reserve`) meets the contracts. What must hold is that
    the growth arithmetic cannot overflow `int`: either the body guards the
    overflow path with a non-returning stop (vec_qcp's `vec_next_capacity` is one
    such guard), or the operation's contract carries a bound clients can meet.
    At a growth branch taken when `size == cap`, a bound on `Zlength l` (such as
    `Zlength l + 8 <= INT_MAX`) suffices, since `rep` exposes only the length.
    Raw libc `malloc`/`realloc`/`free`/`abort` have no contract
    (`verification_stdlib.h` declares none); bodies allocate only through
    step 11.
11. Allocator contracts. For int and pointer elements, call the existing ones
    in `vec_qcp_runtime.h`: `vec_int_array_realloc`, `vec_int_array_free`,
    `vec_ptr_array_realloc`, `vec_ptr_array_free` and `vec_ptr_array_alloc`. Other element types need new trusted
    contracts in a shared header. What must stay: a normal return never fails
    (failure is a non-returning stop such as `vec_resource_stop`), and the
    zero-extent premise (section 10). The in/out `new_cap` is vec_qcp's shape;
    the capacity it returns may be `old_cap + 1`, so a body stores it.

Reuse unchanged: the functors and every lemma in `dynvec_lib.v`,
`vec_buf_ok`, `vec_buf_solve`, and `list_index_lib.v`. Reusing
`vec_next_capacity` and `vec_qcp_runtime.h` is optional.

### What is legitimate client glue

Test for legitimate glue: it says something about *your* program (which list a
vector holds, which slot, a length your model fixes, a field cell). It does not
re-describe size, capacity or buffer, or restate a generic lemma under a new name.

| kind of glue | Example (MiniSat) | where |
|---|---|---|
| a name for a whole table with a length your model fixes | `wlists_rep base n wm := “Zlength wm = 2 * n” && VecpArray.full base (2 * n) wm` | `solver_qcp_model.v` |
| rules that open your table name for the table rules | rules 93/94 (slot or alias on the right) | `solver_qcp.strategies` |
| the meaning of the stored words | `wmap := list (list Z)` | `solver_qcp_model.v` |
| the field cell that holds the table pointer | `solver_wlists_handle s wl` | `solver_qcp_model.v` |
| a slot accessor whose result is `slot(base, i)` | `solver_read_wlist` | `solver_qcp_support.c` |
| a named alias of `rep` on one field, for a contract placed where no annotation names a field of the struct: the public `solver_nclauses_spec` comes before the definition of `struct solver_t` in `solver_qcp.h` | `solver_clauses_rep`, rules 33/34 | `solver_qcp_lib.v`, `solver_qcp.strategies` |
| a client-specific pure side condition | `propagation_destination_ok bound hole target` | `solver_qcp_lib.v` |
| a ghost linking the model to an open slot | `ms_wm(Mscan) == replace_Znth(p, logical_words, scan_wm)` | `solver_propagate` in `solver_qcp_solver_propagate.c` |
| moving your own table name into and out of the library shape | `full_to_wlists_rep`, `missing_i_merge_to_wlists_rep` | `solver_qcp_lib.v` |

Example (MiniSat), an adaptation and not part of DynVec: `solver_array_tail`
(`solver_qcp_model.v`) gives the per-variable arrays and the table of
watch vectors (`solver_wlists_tail`) a ghost physical extent
(the `Given` in `solver_setnvars`) and reuses `vec_buf_ok physical p`, so an array without
extent stores `NULL`.

## 8. Proof-writing guide

Rule zero: **in a client proof, never unfold a DynVec view (`rep`, `rep_ptr`,
`rep_at`, `header`, `shell`) or a `VecArray` predicate (`seg`, `full`,
`missing_i`, `missing2`, `undef_seg`, `undef_missing_i`, `undef_full`).** Use
an intro or fold lemma to close and a strategy or an open lemma to open. The
one exception is the two one-line slot aliases: `unfold VecpArray.vec_store`
turns `VecpArray.vec_store x i l` into `Vecp.rep (Vecp.slot x i) l`, and
`unfold VecpArray.vec_undef_store` turns `VecpArray.vec_undef_store x i` into
`Vecp.shell (Vecp.slot x i)`.

### Which lemma for which step

`partN` below is `Rocq/examples/Applications_human/minisat/solver_qcp_proof_manual_partN.v`;
the vector unit's proofs are in `vec_qcp_proof_manual.v`.

| step | lemma (`dynvec_lib.v`) | example |
|---|---|---|
| close `rep` from an opened header (e.g. after growth) | `rep_intro` | vector unit: `proof_of_veci_push_return_wit_1` |
| close `rep_ptr` from an opened header | `rep_ptr_intro` | Example (MiniSat): `proof_of_solver_propagate_entail_wit_5_1_scan_move` (part11) |
| close `rep_at` from an opened header | `rep_at_intro` | |
| fold or open the three field cells (vector unit bodies and rule proofs) | `header_fold`, `header_open`, `shell_fold`, `shell_open` | vector unit: `proof_of_veci_new_return_wit_1` |
| close an empty vector | `rep_nil_intro`, `rep_empty_intro` | vector unit: `proof_of_vecp_new_return_wit_1` (`rep_nil_intro`), `proof_of_veci_new_return_wit_1` (`rep_empty_intro`) |
| close after truncation | `rep_at_truncate` | vector unit: `proof_of_veci_resize_return_wit_1` |
| forget names | `rep_at_rep`, `rep_at_rep_ptr`, `rep_ptr_rep` | |
| name the buffer / the capacity | `rep_rep_ptr`, `rep_ptr_open`, `rep_open` | Example (MiniSat): `proof_of_solver_analyze_which_implies_wit_37` (part6), `proof_of_solver_lit_removable_return_wit_2` (part9) |
| open to header, live segment and spare tail | `rep_at_open` | |
| get length bounds, keep the predicate | `rep_bounds`, `rep_ptr_bounds`, `rep_at_bounds` | Example (MiniSat): `proof_of_solver_reducedb_safety_wit_13` (part1, `rep_ptr_bounds`) |
| two vectors are distinct | `rep_distinct` | Example (MiniSat): `proof_of_clause_new_which_implies_wit_1` (part4) |
| one slot out of a table and back | `VecpArray.full_split_to_missing_i`, `missing_i_merge_to_full`; at the slot's address `full_split_to_slot`, `slot_merge_to_full` | the table rules 401-409 and 411-416 apply the slot forms; their proofs are in `vec_qcp_strategy_proof.v` |
| second slot out while one is open | `missing_i_split_to_missing2` | Example (MiniSat): `proof_of_solver_propagate_which_implies_wit_39` (part12) |
| second slot back | `missing2_merge_to_missing_i` | Example (MiniSat): `proof_of_solver_propagate_which_implies_wit_45` (part8) |
| peel one uninitialised slot | `undef_seg_unfold` + `Vecp.slot_eq` | Example (MiniSat): `proof_of_solver_setnvars_which_implies_wit_3` (part11) |

The intro lemmas take the header and three separate length arguments
(`n_size`, `n_seg`, `n_undef`), each proved equal to `Zlength l`; a vector in a
struct field is passed by its field address (`&(s # "solver_t" ->ₛ "order")`).
Pass the spelling the program computed and let the side goals carry the
arithmetic. In the vector unit's bodies the left side has the three raw field
cells, so each push return VC first folds them into the header; all of them use
this shape (`proof_of_veci_push_return_wit_1` to `_5` and the `vecp_push`
twins; 10 uses of `rep_intro` in `vec_qcp_proof_manual.v`):

```coq
sep_apply (Veci.header_fold v_pre retval_2 (Zlength l + 1) actual).
sep_apply (Veci.rep_intro v_pre retval_2 (l ++ e_pre :: nil) actual (Zlength l + 1) (cap + 1) (cap + 1)).
all: solve [cancel | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) | vec_buf_solve].
```

A client VC gets the header from the strategies and starts at `rep_intro` or
`rep_ptr_intro`.

The one-slot-to-two-slot split. Example (MiniSat):
`proof_of_solver_propagate_which_implies_wit_39` (part12):

```coq
prop_apply_p (VecpArray.missing_i_index_range wlists_entry p 0 (2 * n) scan_wm). Intros.
prop_apply_p (VecpArray.missing_i_Zlength wlists_entry p 0 (2 * n) scan_wm). Intros.
sep_apply (VecpArray.missing_i_split_to_missing2 wlists_entry p (lit_neg_c candidate)
  (2 * n) scan_wm nil); [ | lia | lia | lia ].
unfold VecpArray.vec_store.
cancel.
```

Get pure facts with `missing_i_Zlength`, `full_Zlength` and
`missing_i_index_range` instead of restating them in the annotation.

### `vec_buf_ok` side goals

`vec_buf_solve` (`dynvec_lib.v`) discharges `vec_buf_ok cap p` from a
hypothesis, from `0 < cap`, or from `p = 0`. Use it as a side-goal finisher:
`[ | first [lia | vec_buf_solve] .. ]`. Example (MiniSat):
`proof_of_solver_propagate_entail_wit_5_1_scan_move` (part11).

### How the strategies make most VCs automatic

`vec_qcp.strategies` has 62 rules: 21 for `Veci`, 24 for `Vecp`, 15 for
`VecpArray` tables and 2 for element segments. By family:

| family | ids (Veci / Vecp) | effect |
|---|---|---|
| open `rep` / `rep_ptr` for a field | 2, 201 / 102, 301 | when a field cell of the same `v` is needed (only the vector unit's bodies): erase the view, add the three cells, `seg`, `undef_seg` and the facts; `rep` also adds a fresh `p` |
| open for a buffer access | 202 / 302 | when a buffer cell or segment at `q == p` is needed: erase `rep_ptr`, add a fresh `cap`, `header`, `seg`, `undef_seg` and the facts |
| full-array handoff | 211 / 311 | the same, handing the element buffer over as `IntArray::full` / `PtrArray::full` |
| close from the header | 212-215 / 312-315 | `rep_ptr` or `rep` on the right and `header` on the left: erase both (with `seg`/`full` and `undef_seg` keyed on the header's length for 212/213 and 312/313); ask `n == Zlength l`, bounds, `vec_buf_ok` |
| close from field cells | 5, 203, 209, 210 / 105, 303, 309, 310 | the same from the three cells (the vector unit's bodies) |
| hide names, name the buffer | 205-207 / 305-307 | convert between views |
| answer a bound | 70, 208 / 71, 308 | prove `0 <= Zlength l` or `Zlength l <= INT_MAX` keeping the predicate |
| shell expose / collect, `UndefStructPred` ↔ shell | 7-10 / 107-110 | split or regroup the three uninitialised cells |
| slot aliases (Vecp) | 116, 95 | without a table on the left: 116 matches `rep(slot(base, i))` against a `rep` held under an alias; 95 closes a slot opened under an alias from its header |
| resize re-close (Vecp) | 35 | close after `resize` with only `vec_buf_ok` left to prove |
| table take-out and refold (`VecpArray`) | 401-409 core(1), 411-416 post(1)/post(3) | section 5, "Strategy rules for a table" |
| element segments read back (`IntArray` / `PtrArray`) | 60 / 68 | cancel a segment on the left against one on the right whose base (and, for 68, bounds) are provably equal: a pointer read back from `begin` is a fresh value equal to the buffer |

So a client annotation says `rep` or `rep_ptr`. When code touches a buffer cell, a
rule opens the vector to `header * seg * undef_seg`; when the post-state needs `rep` back, a
close rule asks only for the pure facts. When code touches one slot of a table,
the table rules take it out and put it back. Manual proofs are left for pure
facts that need real reasoning, intro lemmas after growth in the vector unit,
table slots moving between `missing_i` and `missing2`, and a client's own
table name.

Element-level reasoning uses the framework array library directly
(`IntElems.seg` unfolds to `IntArray.seg`; see the comment on `ARRAY_VIEW`
in `dynvec_lib.v`): view the buffer as `PtrArray::full` and focus a cell with
`PtrArray::missing_i`. Example (MiniSat): the watch-list scan in
`solver_propagate` holds the buffer as `PtrArray::full` and focuses the
scanned cell with `PtrArray::missing_i`.

## 9. Worked patterns

| pattern | Example (MiniSat), solver implementation units |
|---|---|
| push onto a vector field | `veci_push(&s->stack, v)` in `solver_lit_removable` |
| push onto a table slot handed out by a `missing2` split: the accessor returns `slot(base, i)`, the call carries the ghost base | `vecp_push(solver_read_wlist(...) /*@ where rdw_wl = wlists_entry */, *i)` in `solver_propagate` |
| truncate | `veci_resize(&s->tagged, top)` in `solver_lit_removable`; `vecp_resize(&s->learnts, j)` in `solver_reducedb` |
| one slot out, operate, put back, with no annotation | `clause_remove`: `vecp_remove` on two slots |
| slot held open across a loop | `solver_propagate`: `vecp_begin(ws)` (the table rules take the slot out), the scan loop's invariant with `missing_i`, `vecp_resize(ws, ...)` after the loop, then `wlists_rep` again |
| two slots out at once | `clause_new`: `missing2` in a `which implies`, two `vecp_push` calls, refold in a second `which implies` |
| second slot while one is open | `solver_propagate`: split before the `vecp_push` above, put back after it |
| grow a table of vectors | `solver_setnvars`: `wlists_rep` and `VecpArray::undef_seg` before the trusted `minisat_vecp_array_grow` (contract and native form in `minisat_qcp_compat.h`), per-slot `vecp_new` |

DynVec has no grow operation for a table of vectors, and `vec_qcp_runtime.h`
has no table realloc (its allocator contracts are for element buffers). A client
that grows a table writes its own trusted realloc contract over its table name
and `VecArray.undef_seg`, with the zero-extent premise (`vec_buf_ok`) and a
normal return that never fails. Example (MiniSat): `minisat_vecp_array_grow`
Requires `wlists_rep(p, n, wm) * VecpArray::undef_seg(p, 2 * n, physical)` and
`vec_buf_ok(physical, p)`, and Ensures the same table at `__return` with
`undef_seg` up to `2 * actual`; natively it is `vec_checked_grow`.

Keep a table's bound a function-level ghost (a `With` variable), not
`Zlength` of the list, so the heap atom keeps one spelling through a loop.
Example (MiniSat): `solver_propagate` binds `n` in its `With` and writes
`missing_i(wlists_entry, p, 0, 2 * n, ...)`.

## 10. Trust boundary and known limits

**Allocation origin is not represented.** The separation logic here records
which cells a predicate owns, not where they came from. `rep` is cells plus
pure facts, so a client can build `Veci::rep` over a stack array or an interior
pointer. `veci_delete` / `vecp_delete` then meet their contract but not libc
`free`. They are safe only on vectors made by `*_new` and grown by `push`
(the header comments of `vec_qcp.h` and `vec_qcp_runtime.h`). Only an allocation token in the
framework would close this.

**Zero-extent `NULL` premise.** The framework's array predicates are `emp` at
length 0, so a free/realloc contract that owns no cells would accept any
pointer: a double free would verify. In `vec_qcp_runtime.h` the two realloc
contracts therefore require `(old_cap == 0 => p == 0)` and the two free
contracts `(cap == 0 => p == 0)`. This is `vec_buf_ok` written out:
`vec_qcp_runtime.h` includes only `verification_stdlib.h`, not
`vec_qcp_def.h`, so the `vec_buf_ok` Extern is not in scope there. Every vector
operation discharges the premise from `rep_at`, which carries `vec_buf_ok cap p`.

**Runtime contracts are trusted.** `vec_qcp_runtime.h` is the boundary to libc.
`vec_resource_stop` (`Ensure 0 == 1`) is treated as non-returning. In
native mode (`VEC_QCP_NATIVE_RUNTIME`) the same names map to checked `malloc` /
`realloc` / `free`; every translation unit of a native build must use
that mode.

**Table growth is a client contract.** Growing an array of vectors goes
through a trusted contract that the client writes (section 9). Example
(MiniSat): `minisat_vecp_array_grow` (`minisat_qcp_compat.h`), stated
over the client predicate `wlists_rep`.

Other limits:

- Capacity appears in VCs where a vector is opened: every rule that opens
  `rep` or `rep_ptr` adds a fresh existential `cap`, which sits in the
  `header`, and the pure facts `Zlength l <= cap`, `cap <= INT_MAX` and
  `vec_buf_ok cap p`.
- No `VeciArray`. The table rules and slot alias rules 116/95 exist for
  `Vecp` only. The take-out and refold rules cover `full` and `missing_i` from
  slot 0, not `seg`, `missing2` or uninitialised slots.
- `VecArray.seg_to_full` covers a segment from slot 0 only, and no lemma
  splits or merges `undef_missing_i` other than its unfold lemma.
- No `Extern` for `Veci::slot`; no rule relates a raw slot address to `slot`
  outside the table rules 405/406/415/416.
- Element modules and runtime contracts exist only for int and pointer
  elements (no `Int64Elems`, no `vec_<T>_array_realloc` for other types).
  `verification_stdlib.h` has no contract for libc `malloc`, `realloc`,
  `free` or `abort`.
- No layout whose size and capacity are pointers (`begin`/`end`/`cap_end`),
  and no struct with more than the three vector fields.
- No push, grow or element-update lemma in DynVec; growth is closed with
  `rep_intro`. `missing2` is DynVec's own predicate; the framework has no
  two-missing array predicate.
- An opaque name over a framework array predicate, to stop symexec refolding a
  focused cell into its neighbours, is a symexec workaround, not part of the
  abstraction. Example (MiniSat), all in `solver_qcp_lib.v`:
  `propagation_ptr_segment` is `PtrArray.seg` (keeps the scanned watcher apart
  from the prefix segment the scan's `which implies` names),
  `propagation_int_missing` is `IntArray.missing_i` (keeps the written candidate
  literal as a value, so the next read through it finds its cell), and
  `removable_reason_array_hole` is `PtrArray.missing_i` (keeps the read reason
  as a value, so its non-null assertion holds). Spelled as the framework
  predicate, each fails symbolic execution at that step.

## 11. Anti-patterns

| anti-pattern | use instead |
|---|---|
| a hand-rolled vector predicate over size/cap/ptr cells in annotations, or binding `cap` just to name the buffer | `rep` / `rep_ptr` |
| unfolding a DynVec view or a `VecArray` predicate in a client proof | intro, fold and open lemmas, `slot_eq`; `unfold` only the slot aliases `vec_store` / `vec_undef_store` (section 8) |
| case-only hole vocabulary | `VecArray.missing_i` / `missing2` |
| prefix/slot/suffix triple for one open slot | `rep(slot(wl, t), …) * missing_i(wl, t, 0, bound, ls)` |
| pre/post list split with a length alias for the index | one ghost list + `missing_i` |
| bespoke two-hole and uninitialised-run predicates | `missing2`, `VecArray.undef_seg` |
| a hand-written `which implies` that takes one table slot out for a call and puts it back | the table rules 401-409 and 411-416 |
| case-named copies of generic lemmas | `VecArray` lemmas, `list_index_lib.v` |
| bridge lemmas between two vocabularies for the same thing | define the client name directly on the library predicate |
| restating facts the predicates imply | the fact lemma in the proof (`missing_i_Zlength`, `full_Zlength`) |
| hand-unfolding `store_array_rec`, or a `change` of an empty table to its body | `seg_single`, `full_to_seg`, `seg_to_full`, `seg_merge_to_seg`, `full_empty`, `undef_seg_empty` |
| per-instance push lemmas in several proof styles | one `header_fold` + `rep_intro` shape for every push VC |
| struct-specific nested intros | the intro lemmas at the field address |
| a renamed copy of a forbidden lemma | `split_pure_spatial` |
| vector bodies `static inline` in the header: re-verified in every client, and the contracts can fork | a separate verified unit |
| element adapters and vector rules in the client case | `ArrayElems` in `dynvec_lib.v`; the vector's own strategy file |

Each copy or restatement is one more statement symexec carries and one more
proof to maintain.

A conjunct that looks like a restatement can be load-bearing. Before deleting
a conjunct, check that the proof gets every bound it uses without it.
Example (MiniSat): the destination split in `solver_propagate` keeps
`Zlength(scan_wm) == 2 * ms_size(Mscan)` next to `missing_i`. The VC
`solver_propagate_which_implies_wit_39` has
two hypotheses: `propagation_destination_ok (2 * ms_size Mscan) ...`, which
bounds the destination by `2 * ms_size Mscan`, and this conjunct.
`missing_i_Zlength` gives `Zlength scan_wm = 2 * n`; only the conjunct links
`n` to `ms_size Mscan`, which the `j < 2 * n` premise of
`missing_i_split_to_missing2` needs.
