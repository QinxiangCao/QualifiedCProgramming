# Array and String Predicates

This guide covers array, character-buffer, C-string, and string-literal details. Start with built-in resource predicates and add a case-library definition only for an independent, repeated mathematical property.

For a contiguous array, character buffer, C string, or string literal, start with the built-in predicates, then decide whether the problem needs an additional mathematical definition in `formal_case_lib`.

## Common array predicates

Common modules include `IntArray`, `UIntArray`, `CharArray`, `UCharArray`, `ShortArray`, `UShortArray`, `Int64Array`, `UInt64Array`, and `PtrArray`.

Core predicates:

- `TArray::full(p, n, l)`: an array starting at address `p`, of length `n`, whose exact contents are `l`.
- `TArray::seg(p, lo, hi, l)`: the `[lo, hi)` interval relative to the same base address, whose exact contents are `l`.
- `TArray::full_shape(p, n)` / `seg_shape(p, lo, hi)`: accessibility/shape only.
- `TArray::undef_full(p, n)` / `undef_seg(p, lo, hi)`: an uninitialized array or interval.
- The `missing_i` family: intermediate forms produced when a strategy opens one element; do not write these by hand by default.

Array reads and writes usually require explicit bounds such as `0 <= i && i < n`.

`TArray::full(p, n, l)` already supplies `Zlength(l) == n` and `0 <= n`; resources such as `TArray::seg(p, lo, hi, l)` likewise supply their own interval and length facts. Do not repeat those facts in the same specification or annotation. An access bound here says that the current index is legal; it is distinct from the array length already carried by the resource.

## Choosing a predicate

Use `TArray::full(p, n, l)` when:

- The specification or invariant discusses `Znth`, `sublist`, `replace_Znth`, `Permutation`, `sum`, or sortedness.
- The function's result depends on element values.
- A postcondition must precisely describe the list after an in-place update.
- A refinement or pure specification explicitly uses a list value as its abstract state.

Typical annotation clues:

```c
ret == sum(sublist(0, i, l))
Permutation(l, l1) && increasing(l1)
v == Znth(i, l, 0)
new_l == replace_Znth(i, v, l)
```

Use `TArray::full_shape(p, n)` or `seg_shape(p, lo, hi)` when:

- Only memory existence, length, and accessibility matter.
- The program reads or writes elements, but the goal does not depend on their values.
- The postcondition requires only a valid destination buffer.

Shape predicates fit memory-layout or buffer-existence goals. If later reasoning needs `sum(l)`, `Permutation`, `sublist`, or element bounds, shape is insufficient; use an exact-content predicate.

Use `TArray::seg(p, lo, hi, l)` for:

- Multi-cursor or two-pointer algorithms.
- An array partitioned into a prefix, current interval, and suffix.
- Merge, partition, copy, window, and similar algorithms that maintain adjacent intervals.

Typical shape:

```c
IntArray::seg(a, 0, i, left_part) *
IntArray::seg(a, i, j, middle_part) *
IntArray::seg(a, j, n, right_part)
```

When a loop has several cursors such as `i / j / k` and each corresponds to a distinct logical interval, `seg` is usually more robust than one enormous `full` assertion plus pure `sublist` equalities.

For an initially uninitialized buffer that is filled incrementally, begin with `TArray::undef_full(p, n)`. During the loop, maintain a written prefix using `seg` / `seg_shape` and an unwritten suffix using `undef_seg`. Before leaving the function or local scope, the state should expose a complete `full` or `undef_full`.

If an offset pointer becomes the main base for later accesses to a suffix, it may be used directly as the base address. If the suffix must still be composed with other intervals of the original array, `seg(p, i, n, suffix)` is usually better.

## C-string predicate

```coq
store_string : Z -> list Z -> Assertion
```

`store_string(p, s)` denotes a readable and writable C-string buffer. Its logical content `s : list Z` excludes the terminating zero, while the underlying memory contains `s ++ [0]`. Prefer it when the program semantics are those of a C string. If the proof needs the underlying character intervals, use `CharArray::full` / `CharArray::seg`.

## String-literal predicates

```coq
store_stringLit : Z -> string -> Assertion
GlobalStrings : (string -> Z) -> Assertion
```

`store_stringLit(addr, s)` denotes a string literal. It is not suitable for a writable local array such as `char a[] = "abc"`. `GlobalStrings(LitMap)` denotes the pool of literal addresses and can be split to obtain `store_stringLit(LitMap("..."), "...")`. Do not assume by default that distinct literals have distinct addresses unless the current case specification says so.

## Recommendations

- For ordinary `int`, `uint`, and pointer arrays, choose among `full`, `seg`, `shape`, and `undef_*` as described above.
- When `char *` is a C string and the proof uses logical contents without the terminator, use `store_string(p, s)`.
- When a character array is merely a byte array, use `CharArray::full` / `seg` / `undef_*`.
- Before reading a string literal, provide `GlobalStrings(LitMap)` or an already-split `store_stringLit`.
- Do not treat a Rocq `string` directly as a `list Z`; use the appropriate conversion when a memory list is required.
- Array predicates express resource ownership, while `Znth` observes a position in the logical list. Do not use `Znth` in place of the array predicate itself.
- After a single-element read or write, retain the bounds, array resource, and current value binding together—for example, `0 <= i < n`, `IntArray::full(a, n, l)`, and `v == Znth(i, l, 0)`.
- For segmented writes or two-pointer algorithms, continue to maintain `full` / `seg` / `undef_*` resource shapes first, then describe content changes with `sublist`, `replace_Znth`, and `Znth`.
- Do not assume a universal `Zhth` foundation library exists. If a case provides a similar observation predicate, treat it only as a local interface; do not reduce the core invariant semantics to manipulating that interface.

## Limits on direct `missing_i` use

`missing_i`, `missing_i_shape`, and `undef_missing_i` are normally intermediate forms produced when a strategy opens one element, not the default form for handwritten annotations.

Do not write `missing_i` just because the code contains `a[i]` or `a[i] = v`. Start with the higher-level `full`, `seg`, `shape`, or `undef_*` form and let array strategies split and restore it. Expose `missing_i` directly only when the specification truly needs to express “the remainder of the array except element `i`.”

## `Znth` and high-level properties

Use `Znth` to observe a position; use an array predicate to express resource ownership. They are not substitutes for one another.

Appropriate places for `Znth` include:

- Binding a local value after an array read.
- The current candidate, pivot, or boundary element.
- Connecting the states before and after a `replace_Znth` write.

Do not turn an invariant into a long sequence of isolated `Znth` equalities. Express “`best` is the maximum of the processed prefix” with `sublist` and `max_value_of_subset` from `MaxMinLib`. Express partition properties with `Forall`, `sublist`, and existing bound predicates first. A necessary business predicate also reuses the specified library semantics and contains no resources, input ranges, or execution-safety conditions.

If a proof appears to require new foundational array/string memory semantics, first confirm that no built-in predicate already provides them. If the annotation chose the wrong predicate, repair the annotation instead.

## Growable vectors

A struct holding an element count, a capacity, and an element-buffer pointer is a growable vector. Describe it with the vector library, `DynVec` and `VecArray` in `Rocq/examples/Applications_human/dynvec_lib.v`, never with a predicate over its fields. The existing instances `Veci`, `Vecp`, and `VecpArray` (an array of `vecp_t`) are in `Rocq/examples/Applications_human/minisat/vec_qcp_lib.v`, for a target C that already includes `QCP_examples/Applications_human/minisat/vec_qcp.h`. That header declares the C structs `veci_t` (int elements) and `vecp_t` (pointer elements) and the operation contracts that clients see.

| View | Meaning | Use |
|---|---|---|
| `Veci::rep(v, l)` | `v` holds `l`; buffer and capacity hidden | the default; any call that may grow the vector; inside larger struct predicates |
| `Veci::rep_ptr(v, p, l)` | also names the buffer `p` | after `veci_begin`, walking or writing elements in place |
| `Veci::shell(v)` | the three uninitialized fields | before `*_new`, after `*_delete` |

`Vecp::` works the same way. `rep_at`, which exposes the capacity, and `header`, the struct the strategies leave while a buffer is open, never appear in annotations; annotations use `rep`, `rep_ptr`, and `shell`, which keep the capacity hidden. Contents are a `list Z` (int values or Z addresses), changed with existing list operations: push gives `rep(v, app(l, cons(x, nil)))`, an in-place write `replace_Znth(j, w, l)`, a resize `sublist(0, k, l)`. `rep` and `rep_ptr` already imply `0 <= Zlength(l) <= INT_MAX`; do not restate it. The `vec_qcp.h` push requires no length bound.

For an array of `vecp_t`, write the whole table as `VecpArray::full(tbl, m, ls)` directly, with case facts such as the table length in a case predicate beside it. The table rules of `vec_qcp.strategies` handle one slot automatically: when `0 <= i < n` is provable and the code needs the `Vecp::rep`, `rep_ptr`, or a field of `Vecp::slot(tbl, i)`, of an alias `w == Vecp::slot(tbl, i)`, or of `&tbl[i]`, they take the slot out and leave `VecpArray::missing_i`, and once the slot is back as a `Vecp::rep` they fold `full` again (with `replace_Znth` if its contents changed). Write by hand the shapes these rules do not cover: two slots out at once as `VecpArray::missing2` (when the code updates two slots of one table between two folds), a slot held out across a loop as `Vecp::rep_ptr(...) * VecpArray::missing_i(tbl, i, 0, m, ls)` in the Inv Assert, and a `missing_i` that does not start at slot 0. Hand back to main a case table predicate whose body is `VecpArray.full` (the table rules need a strategy rule that opens it) and a segment that does not start at slot 0 (`vec_qcp_def.h` exports no `VecpArray::seg`). `DYNVEC.md` section 5 lists the cases with examples. Describe an uninitialized tail with `VecpArray::undef_seg`. Bound the table with a ghost expression such as `m`, not `Zlength(ls)`. `missing_i` and `missing2` are the only hole shapes.

- The target C must already `#include "vec_qcp.h"`. Never copy `vec_qcp.h`, `vec_qcp_def.h`, or `vec_qcp.strategies` into a case, and do not repeat the `Extern` declarations of `vec_qcp_def.h`. When a case predicate in `formal_case_lib` mentions the vectors, import them there with `From SimpleC.EE.Applications_human.minisat Require Import vec_qcp_lib.`. Under dune, the import needs the case's dune `coq.theory` to be or list `SimpleC.EE.Applications_human` (a case under `Rocq/examples/Applications_human`); a case elsewhere hands it back to main.
- Case-specific adaptation is allowed: a pure case predicate beside a library predicate that states case facts (for example the table length), a slot-index function, or pure index facts. Not allowed: a predicate over the size/cap/ptr cells or the buffer, an alias that only renames a library predicate, or a case copy of a library lemma.
- Another vector struct (other struct or field names, another element type, or the program's own push/grow code) needs a new `DynVec` instance with its own strategies and verified operation unit, which main writes. Record in `agent_output.md` the struct and field names, the element type, the operations the client calls with their contracts (`shell` to `rep(v, nil)` for init, `rep(v, l)` to `rep(v, app(l, cons(x, nil)))` for push), raw `malloc`/`realloc`/`free`/`abort` calls, growth arithmetic that can overflow `int`, and the fields the client accesses directly or local vector structs whose address is taken (the new strategies need rules for both); then stop with an infrastructure blocker (workflow §7). The growth policy itself (`cap + 8`, doubling) is free, because `rep` hides the capacity.
- A layout `DynVec` cannot express (size or capacity not C `int`, a `begin`/`end`/`cap_end` pointer triple, extra fields, an inline buffer) is a library gap. Hand it back the same way, naming the mismatch, without a case predicate over the fields.

Wrong:

```c
store(&(v->size), n) * store(&(v->cap), c) * store(&(v->ptr), p) *
IntArray::seg(p, 0, n, l) * IntArray::undef_seg(p, n, c)
```

Right:

```c
Veci::rep_ptr(v, p, l)
```
