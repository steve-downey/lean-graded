# handoff → compose-applicative

Goal and merge criterion: fixed by `step-compose-applicative.md`.

## No dependency on [canonical-representation]

`Graded/Canonical.lean` (`Canon`, `canonEquiv`, `docs/design.md#representation`)
touched only the `#representation` anchor — nothing in `#compose`,
`#traverse`, `#applicative`, `#grade`, or `#carrier`, which are your
step's own listed dependencies, changed underneath you. `Canon` has no
`pure`/`bind`/`ap` and is not a second grade; there is no connection
between "sorting error kinds" and "composing graded applicatives" at
this stage. Do not go looking for one.

## Merge commit

`step/canonical-representation` merged into `integration/lean-model` at
`ccde746` (`--no-ff`; the step's own commit is `6619541`). The merge was
a clean `ort` fast-forward-style merge with no conflicts (the two
branches touched disjoint files); `integration/lean-model` was GREEN in
the worktree immediately before merging (`make verify`, `make nosorry`,
`make letters` all exit 0), and the merge changed nothing the build
depends on outside the new files.

## `abbrev` vs `def` for a type synonym you plan to build instances through

Your step's `Comp (g h : Grade Err) (α : Type u) : Type u := Graded g
(Graded h α)` is written as a `def` in the step file. If anything later
in your step needs a typeclass instance (`DecidableEq`, `Repr`, etc.) to
be found *for* `Comp g h α` by unifying it with an instance stated for
`Graded g (Graded h α)`, a plain `def` will not do it — Lean's instance
search does not unfold ordinary `def`s, only `abbrev`/`@[reducible]`
ones. This model's own `Grade := Finset Err` is declared `abbrev` for
exactly this reason. I hit this concretely this step: my `Canon` was
originally a `def`, and `DecidableEq (Canon Err)` (needed for `#guard`)
could not be found until I changed it to `abbrev`, even though nothing
else in the definition changed. If your test file's `#guard`s on `Comp`
values fail to typecheck with a "type mismatch ... expected Bool" or a
missing-instance error, this is the first thing to check — not a sign
your definition is wrong.

## Still-live elaboration gotchas (twelve steps in)

None of these are new; they are still live and still not written down
anywhere your step file points you to, so they are repeated here rather
than assumed:

- A bare `pure` inside `Tests/*.lean` or `Examples/*.lean` is ambiguous
  between `Graded.pure`, `Accum.pure`, and Mathlib's `Pure.pure` (your
  step adds a third carrier, `Comp`, which may add a fourth candidate if
  you give it its own `pure` name reachable by dot notation) — write the
  fully-qualified name explicitly at every such use site.
- `pure`/`Grade.bot` with no other `Graded`-typed argument nearby leaves
  `DecidableEq Err` stuck ("typeclass instance problem is stuck"). Fix
  with a full type ascription at the use site. `Comp.pure`'s definition
  (`Graded.ok (Graded.ok a)` at grade `(Grade.bot, Grade.bot)`) is
  exactly this shape and may need one.
- `#guard`/`=` comparing two `Graded g α` (or `Accum g α`) values
  directly has not worked in any step so far; route through a
  render-to-`String` function, as every step since [monad-laws] has.
  Untested whether this extends to `Comp g h α` (nested `Graded`) — budget
  for it needing the same treatment, doubled (render the outer, which
  itself needs to render the inner).
- `#guard` cannot carry a `/-- ... -/` doc comment; use a plain `--`.
- `cast_ok`/`cast_err`/`cast_widen` live in `Graded/Monad.lean`;
  `cast_cast` (composing two casts along a transitive grade equality) is
  in `Graded/Carrier.lean`. Every law-heavy step since [monad-laws] has
  cited at least one; your applicative laws and `traverseComp_eq`/
  `flatten_ap` are exactly this kind of step.

## Do not use `git add -A` in the main checkout

The main checkout's working tree still carries an uncommitted editorial
pass across the pre-[graded-morphism] letters under `blog/letters/`
(confirmed still present after this step's merge), made by the
repository's owner and deliberately left uncommitted. Stage your own
files by name in the main checkout; `git add -A` is fine inside your own
worktree only.

## Your step file specifies `Comp` as a `def` — make it an `abbrev`

`Graded/Canonical.lean` had to change `Canon` from `def` to `abbrev`
because Lean's instance search does not see through a plain `def`:
anything needing a `DecidableEq`/`LinearOrder` instance on the underlying
type fails to resolve it. `Grade` itself is an `abbrev` for the same
reason. `step-compose-applicative.md` writes

```lean
def Comp (g h : Grade Err) (α : Type u) : Type u := Graded g (Graded h α)
```

which will hit this the moment anything needs an instance through it.
Write it as an `abbrev`. This is a correction to your step file, not a
deviation from it — record it in your metrics note.
