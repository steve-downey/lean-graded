# handoff → compose-flatten

Goal and merge criterion: fixed by `step-compose-flatten.md`.

## Dependencies are untouched

`Graded/Grade.lean` (`join_assoc`, `join_comm`, `join_idem`, `le_join_left`,
`le_join_right`, `join_le`, `join_mono`, `bot_le`, `le_refl'`, `le_trans'`,
`join_eq_right_of_le`), `Graded/Carrier.lean` (`Graded`, `map`, `cast`,
`cast_rfl`, `cast_cast`), `Graded/Widen.lean` (`widen`, `fromEmpty`,
`widen_irrel`, `widen_widen`, `widen_map`, `widen_cast`),
`Graded/Monad.lean` (`pure`, `bind`, `bind_pure_left`, `bind_pure_right`,
`bind_assoc`, `bind_map`, `bind_widen`, and — note the location —
`cast_ok`/`cast_err`/`cast_widen`, which live here, not in `Carrier.lean`),
`Graded/Applicative.lean` (`ap`, `apFlipped`, `map2`, the four laws,
`ap_flip`), `Graded/Accum.lean`, and `Graded/Traverse.lean` (`foldGrade`,
`traverse`, `traverse_cons`) are byte-for-byte what
[applicative-accumulation]/[traverse-list] left them.
`docs/design.md`'s `#monad`, `#subsumption`, `#grade`, `#applicative`
sections are untouched by this step.

## `docs/design.md#traverse` now has a `### Tuple` subsection

This step added a `### Tuple: the grade is computed once, at the type
level` subsection to `#traverse`, between the existing `### List` content
and the `## compose` heading. If you open `#traverse` per your step
file's pointer you'll see it — it's not relevant to `compose-flatten`
(it's about the fixed-size tuple case, nested-carrier composition is a
different question), just don't be surprised by its presence between
what you're citing and the `## compose` heading you'll be filling in.

## `Graded/Prelude.lean` is no longer just the shared-imports stub

This step added `HList` (a plain recursive `Type`-valued `def`, not an
`inductive` — see the reason in `Graded/Tuple.lean`'s module docstring if
curious, but it's not relevant to nested-carrier flattening) plus
`HList.nil`/`HList.cons` to `Graded/Prelude.lean`. Your step's declared
scope doesn't touch `Prelude.lean` and shouldn't need to — `flatten`
doesn't need a heterogeneous product — but every module still imports it,
so if you ever inspect it, the stub now has content. Do not add a second
product-shaped helper there without checking what's already there first.

## `Examples/Validation.lean` — where your consumer lands

This step appended a `sequence`/tuple consumer section (`validateTuple`,
`renderTuple`, starting after a `-- ---...---` divider comment, right
before the file's closing `end Examples.Validation`) to the *end* of
`Examples/Validation.lean`, after the existing `traverse`/`renderNats`
section. Your `lookup : String → Graded {io} (Graded {parse} Nat)`
consumer will append *after* mine — the file currently ends (right before
`end Examples.Validation`) with:

```
#guard renderTuple (validateTuple "42" 9999) = "err Examples.Validation.E.range"

end Examples.Validation
```

Insert your section between that `#guard` line and `end
Examples.Validation`; don't reorder or touch the tuple section above it.

## Naming has no collisions

This step's public names are `GList`, `GList.nil`, `GList.cons`,
`joinAll`, `joinAll_perm`, `joinAll_dedup`, `join_mem_eq`, `sequence`,
`sequence_nil`, `sequence_cons`, plus `HList`/`HList.nil`/`HList.cons` in
`Prelude.lean`. None of these collide with `flatten`, `swap`, `Compose`,
or anything else your step file names.

## Two elaboration gotchas from two steps back, still live

Inherited from [traverse-tuple]'s own inbound handoff and confirmed still
relevant (this step's `flatten_pure_outer`/`flatten_pure_inner` both
involve bare `pure`, same shape as this step's `sequence_nil` did):

- A bare `pure` inside `Tests/*.lean` or `Examples/*.lean` is ambiguous
  between `Graded.pure` and the generic `Pure.pure` — write `Graded.pure`
  explicitly at every use site there. (Inside `namespace Graded` itself,
  bare `pure` resolves fine — only test/example files outside the
  namespace need the qualification.)
- `pure`/`Grade.bot` with no other `Graded`-typed argument nearby can
  leave `Err`'s `DecidableEq` instance stuck ("typeclass instance problem
  is stuck"). Fix: annotate explicitly with a full `Graded g α` type
  ascription at the use site.
- `#guard`/`=` comparing two `Graded g α` values directly has not worked
  in any step so far; route through a render-to-`String` function (this
  step added `renderTuple`; yours will need its own, since your `lookup`
  consumer's payload/grade shape is different again).

## Merge commit

`step/traverse-tuple` merged into `integration/lean-model` at
`503b3d0` (`--no-ff`; the step's own commit is `cc57109`).
`integration/lean-model` is GREEN (`make verify`, `make nosorry`, `make
letters` all exit 0) as of that commit.

## One finding not needed by this step, recorded for completeness

`joinAll_perm`/`joinAll_dedup` (tuple order-independence vs. dedup) split
along commutativity+associativity vs. idempotence, mirroring
[traverse-list]'s `foldGrade_le`/`foldGrade_cons_ne_nil` split — but this
has no bearing on `compose-flatten`'s product-pomonoid question, since
nested-carrier flattening isn't folding a list of grades at all.
