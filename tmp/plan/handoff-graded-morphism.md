# handoff → graded-morphism

Written by the orchestrator, not by [compose-flatten]. That step halted
on a partial block before writing its own handoff, so this covers what
you need from it and what the halt means for you.

Goal and merge criterion: fixed by `step-graded-morphism.md`.

## [compose-flatten] merged, minus one theorem

`Graded/Compose.lean` exists and is green: `flatten`, `swap`, and eight
laws (`flatten_eq_bind_id`, `flatten_map`, `flatten_pure_outer`,
`flatten_pure_inner`, `flatten_flatten`, `flatten_widen_outer`,
`flatten_widen_inner`, `flatten_comm`). Its traverse composition law was
**refuted** — see the open question `graded-traversable-composition` at
`docs/design.md#compose`. Nothing in your step depends on it: your
naturality law is about `rename` commuting with `traverse`, a different
law over a single carrier, and it is not affected by the composition
question. Do not try to fix or revisit the composition law; it is
recorded and deferred by decision.

`tmp/plan/blocked-compose-flatten.md` exists on disk. It is not on your
read path and you do not need it.

## `flatten_comm` needs no hypothesis — do not import the wrong pattern

Two earlier steps found an "at most one side is an error" hypothesis
(`(∃ f', f = .ok f') ∨ (∃ a, x = .ok a)`) for `ap_flip` and for `Accum`.
`flatten_comm` was expected to be a third instance and is **not**: it
holds unconditionally, because a nested `Graded g (Graded h α)` has three
inhabited shapes and can never hold two errors at once. If your
`rename_toGraded` or a naturality proof looks like it wants that
hypothesis, check whether the two things you are combining are genuinely
independent before adding it. Adding an unnecessary hypothesis is a
weakened statement, which is a halt condition, not a convenience.

## A universe constraint you may meet

`Graded/Compose.lean` quantifies its payload types at `Type u` — the same
universe as `Err` — rather than the `Type v` used elsewhere, because
`Graded h α` lives in `Type (max u v)` while `bind` ties its two payload
type variables to one universe. That workaround is scoped to that file
only. Your `Graded/Morphism.lean` introduces a *second* error type
(`Err' : Type u`) rather than a second payload universe, so you may not
hit this at all — but if you get an unexplained universe error around
`bind` or `traverse`, this is the shape of the problem and pinning the
payloads to `Type u` is the known fix.

## Where your consumer goes in `Examples/Validation.lean`

The file now ends, right before `end Examples.Validation`, with the
`lookup`/`flatten` consumer section that [compose-flatten] appended after
the tuple section. Insert your `rename` consumer between that section's
last `#guard` and `end Examples.Validation`. Do not reorder or edit the
sections above yours.

## Three elaboration gotchas, still live after ten steps

- A bare `pure` inside `Tests/*.lean` or `Examples/*.lean` is ambiguous
  between `Graded.pure` and Mathlib's `Pure.pure` — write `Graded.pure`
  explicitly there. Inside `namespace Graded` it resolves fine.
- `pure`/`Grade.bot` with no other `Graded`-typed argument nearby leaves
  `DecidableEq Err` stuck ("typeclass instance problem is stuck"). Fix
  with a full type ascription at the use site.
- `#guard`/`=` comparing two `Graded g α` values directly has not worked
  in any step. Route through a render-to-`String` function; every step so
  far has written its own (`renderN`, `renderSum`, `renderPair`,
  `renderNats`, `renderTuple`, and [compose-flatten]'s). Yours will need
  one too — your payload and grade shape differ again.
- `#guard` cannot carry a `/-- ... -/` doc comment; use a plain `--`.

## Do not use `git add -A` in the main checkout

The main checkout's working tree has an uncommitted editorial pass across
all ten existing letters under `blog/letters/`, made by the repository's
owner and deliberately left uncommitted. `git add -A` for your bookkeeping
commit would sweep those into your commit. Stage your own files by name
instead. Inside your worktree `git add -A` is fine — the edits are not
there.

## `cast_ok`/`cast_err`/`cast_widen` live in `Graded/Monad.lean`

Not in `Carrier.lean`, where you might look for them. They close casts
that meet a constructor or a `widen`, and every law-heavy step since
[monad-laws] has used them.

## Merge commit

`step/compose-flatten` merged into `integration/lean-model` at `4f96527`
(`--no-ff`; the step's own commit is `ec34bce`). Subsequent commits on the
branch record the block and the open question. `integration/lean-model` is
GREEN (`make verify`, `make nosorry`, `make letters` all exit 0).
