# Array and String Predicates

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

Do not turn an invariant into a long sequence of isolated `Znth` equalities. If the intended property is “`best` is the maximum of the processed prefix” or “the current interval satisfies the partition condition,” define a business predicate such as `PrefixMaxState(sublist(0, i, l), best)` or `PartitionedAround(l, lo, mid, hi, pivot)`.

If a proof appears to require new foundational array/string memory semantics, first confirm that no built-in predicate already provides them. If the annotation chose the wrong predicate, repair the annotation instead.
