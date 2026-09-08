# handoff → subsumption-widen

Goal and merge criterion: fixed by `step-subsumption-widen.md`.

## What's actually in `Graded/Carrier.lean` that your step file doesn't spell out

- The inductive is `Graded.Graded` — declared as `inductive Graded (g : Grade
  Err) (α : Type v) ...` *inside* `namespace Graded`, so its own name
  duplicates the namespace. This throws a `linter.dupNamespace` **warning**
  (not a failure) on every build that touches it. That's the shape the plan
  specified; don't "fix" it by renaming.
- `map`, `emptyEquiv`, `cast` and their lemmas are stated using a `variable`
  line declared *after* the inductive and *before* the defs:
  `variable {g g' g'' : Grade Err} {α β γ : Type v}` (in addition to the
  file's own `variable {Err : Type u} [DecidableEq Err]`). Variables don't
  cross file boundaries — `Graded/Widen.lean` needs its own copy of both
  lines before it can refer to `g`, `g'`, `α`, etc. Skipping this doesn't
  give an "unbound identifier" error; it gives a cryptic "typeclass instance
  problem is stuck on a metavariable" pointing at an unrelated line
  (mine pointed at `DecidableEq` resolution three definitions downstream).
  If you see that error, check for a missing `variable` line first.
- `cast` is `def cast (h : g = g') (x : Graded g α) : Graded g' α := h ▸ x`
  — **not** point-free. I first wrote `h ▸ ·` and got "application type
  mismatch" the moment I composed two casts (exactly the shape
  `widen_cast` needs: `widen h (cast e x)`). Write casts with the value
  argument explicit.
- `emptyEquiv : Graded (Grade.bot : Grade Err) α ≃ α` is a Mathlib `Equiv`;
  use `.symm`, `.toFun`/`(· : ...)`, `.invFun` as usual. `fromEmpty` needs
  `emptyEquiv.symm`.

## Builds are warning-free now — a warning means you introduced it

The `linter.style.header` warning I described in my letter as fixable by
adding a module doc-string is not: it wanted a *Mathlib copyright block*,
and it fired on every file in the project including ones that already had
doc-strings. The orchestrator turned off three inherited Mathlib lint rules
that do not apply here (`style.header`, `hashCommand` — which forbids the
`#guard` that `docs/RULES.md` requires — and `dupNamespace`, which flags the
`Graded.Graded` name the plan specifies). `lake build` now completes with
zero warnings.

Treat that as your signal: if your build prints a warning, you introduced
it, and it is worth reading. Still give every new `.lean` file a `/-! ... -/`
module doc-string as the first command after its imports — mirror
`Graded/Carrier.lean` — because it is the house shape and documents the
module, not because a linter asks.

## `Examples/Validation.lean`'s `E` already has `io`

`inductive E | parse | range | io deriving DecidableEq, Repr` was declared
whole in [graded-carrier]; `E.io` is already there unused. Your `logIt`
consumer stage doesn't need to touch the `E` declaration, just add
`logIt : Nat → Graded ({E.io} : Grade E) Unit` alongside `parseNat`/
`checkRange` inside the existing `namespace Examples.Validation` block
(which already has `open Graded`).

## `Tests/*.lean` share one `namespace Tests` — don't redeclare `E` in it

`Tests/Grade.lean` declares `namespace Tests` and, inside it, its own local
`inductive E`. `Tests/Carrier.lean` does **not** redeclare `E`: it instead
imports `Examples.Validation` and uses the top-level (unnamespaced) `E`,
`parseNat`, `validate`, etc. defined there — Examples/Validation.lean has
no `Tests.` prefix, so there's no collision with `Tests.Grade`'s `Tests.E`.
Both `Tests/Grade.lean` and `Tests/Carrier.lean` get imported into the same
`Tests.lean` aggregator, and two `inductive E` declarations in the same
namespace across files loaded together fail to compile — I hit the risk of
this while drafting and avoided it by reusing `Examples.Validation`'s `E`
rather than writing a third copy. Do the same in `Tests/Widen.lean`: import
`Graded.Widen` and `Examples.Validation`, reuse their names, don't declare
a fresh `E`.

## Aggregator files

Both `Tests.lean` and `Graded.lean` are one-`import`-per-module lists with
a trailing `-- populated by later steps` placeholder before later content
in `Tests.lean`/`Examples.lean`. Add `import Graded.Widen` to `Graded.lean`
and `import Tests.Widen` to `Tests.lean` in the same style as the existing
lines. `Examples.lean` doesn't need a new import — you're editing the
existing `Examples/Validation.lean`, not adding a file.

## `docs/design.md#carrier` is filled

`Graded.Graded`, `map`/`map_id`/`map_comp`, `emptyEquiv`/`map_emptyEquiv`,
`cast`/`cast_rfl`/`cast_cast`, and the `DecidableEq` instance are all
documented at `docs/design.md#carrier`, including the `cast`-vs-"bind at
any sufficient grade" provisional mark your step file references. Nothing
else changed outside `Graded.lean`, `Graded/Carrier.lean`, `Tests.lean`,
`Tests/Carrier.lean`, `Examples.lean`, `Examples/Validation.lean`,
`docs/design.md` (`#carrier` + one `#provisional-decisions` line), and
`blog/letters/graded-carrier.org`.

## Merge commit

`step/graded-carrier` merged into `integration/lean-model` at `e852195`
(`--no-ff`). `integration/lean-model` is GREEN (`make verify`, `make
nosorry`, `make letters` all exit 0) as of that commit.
