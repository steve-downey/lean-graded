# handoff → grade-pomonoid

Goal and merge criterion: fixed by `step-grade-pomonoid.md`.

## Lake syntax surprise

The Mathlib `math` template (as of this bootstrap) generates
`lakefile.toml`, not `lakefile.lean`. This repo's lakefile is TOML:

```toml
[[lean_lib]]
name = "Graded"

[[lean_lib]]
name = "Tests"

[[lean_lib]]
name = "Examples"
```

Your step file's spot check `grep -n "instance" Graded/Grade.lean` and
`grep -c "PROPERTY:"` are unaffected (they target the `.lean` file, not the
lakefile), so nothing in your step needs to touch `lakefile.toml`. Just
don't go looking for `lean_lib Graded` syntax in a `lakefile.lean` — it
isn't there.

## Import for Finset

`Graded/Prelude.lean` already has `import Mathlib.Data.Finset.Basic` at the
top of the file (imports must precede any other command, including the
module doc-comment — Lean rejected an import placed after a `/-! -/` block
with "invalid 'import' command, it must be used in the beginning of the
file"; the doc-comment now comes after the import). `Finset.Basic` was
sufficient to build cleanly with Mathlib's `∪`, `⊆`, and `∅` on `Finset`
available; I did not need `Mathlib.Data.Finset.Lattice`. If a specific
lemma name from your list (`join_mono`, `join_le`, etc.) isn't found under
`Finset.Basic`'s namespace, that's the first place to widen the import —
try `Mathlib.Data.Finset.Lattice` before anything heavier.

## Toolchain and cache

`lean-toolchain`: `leanprover/lean4:v4.34.0-rc2`. Mathlib pinned at commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0` (see `docs/design.md#toolchain`).
The full Mathlib oleans cache (`.lake/packages/*/`) already lives at
`/home/sdowney/src/lean-graded/.lake` — your setup step's `ln -s
/home/sdowney/src/lean-graded/.lake .lake` will pick it up; you should not
need to run `lake exe cache get` again.

## Warm verify time

`make verify` on an unchanged tree: 4 seconds (611 jobs, all replayed).
Cold (`rm -rf .lake/build`, packages cache untouched): 12 seconds. Both
numbers are in `docs/design.md#toolchain` and in the `verify-floor` row of
`tmp/plan/metrics.jsonl`.

## One thing to know before you write Tests.lean

Root `Tests.lean` currently contains only `-- populated by later steps` and
a trivial `example : True := trivial`. Add `import Tests.Grade` to it
alongside that line (don't remove the trivial example — nothing requires
its removal and it costs nothing to keep as a smoke check).

## Minor, non-blocking Makefile note

`make nosorry`'s grep invocation names bare paths `Graded Tests Examples`.
Right now `Tests` and `Examples` are root **files** (`Tests.lean`,
`Examples.lean`), not directories, so `grep -r ... Tests Examples` prints
`No such file or directory` for those two on stderr; the `!`-negation still
reports `nosorry=0` correctly (verified: inserting and removing a real
`sorry` in `Graded/Prelude.lean` behaves correctly today, since `Graded` is
a real directory and is genuinely scanned). Once your step creates
`Tests/Grade.lean`, `Tests` becomes a real directory and the stderr noise
for it disappears on its own. This is cosmetic, not a block — flagging it
so you don't mistake the stderr line for a real failure.
