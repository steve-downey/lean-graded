# handoff → canonical-representation

Goal and merge criterion: fixed by `step-canonical-representation.md`.

## No dependency on [graded-morphism]

`Graded/Morphism.lean` (renaming/coarsening error kinds, `docs/design.md#morphisms`)
does not touch anything this step needs. Your step's own listed
dependencies (`docs/design.md#grade`, `#traverse`'s `joinAll_perm`) are
unaffected by it. Do not go looking for a connection between "grade
morphisms" and "canonical representation" — there isn't one at this
stage; they are independent facts about `Grade`.

## Merge commit

`step/graded-morphism` merged into `integration/lean-model` at `381b67c`
(`--no-ff`; the step's own commit is `16ad8cc`). `integration/lean-model`
is GREEN (`make verify`, `make nosorry`, `make letters` all exit 0).

## A dependently-typed elaboration gotcha you will likely hit

`Canon := { l : List Err // l.Sorted (· < ·) }` and `canonEquiv : Finset
Err ≃ Canon Err` both build values whose *type* is indexed by a proof
(`Sorted`, or an `Equiv`'s round-trip obligations). If you construct such
a proof by directly embedding a Mathlib lemma inline inside a
constructor or `Subtype.mk` — e.g. `⟨Finset.sort (· ≤ ·) s, <some Mathlib
sortedness lemma applied inline>⟩` — the *elaborated* term can end up
typed using whatever name/form that Mathlib lemma's own conclusion is
stated in, not the name you wrote in your own `Canon`/`canonEquiv`
declarations, even when the two are definitionally equal. `rw`/`simp`
later fail to match it against lemmas stated in your own vocabulary,
with an error that looks like "not type-correct under implicit
transparency" pointing at two things that look identical. [graded-morphism]
hit exactly this with `Finset.mem_image_of_mem` feeding a `Graded.err`
constructor; the fix was a one-line wrapper theorem
(`Grade.mem_rename` in `Graded/Morphism.lean`) that restates the borrowed
fact with its conclusion pinned to your own name, and builds every
downstream term from that wrapper instead of the raw Mathlib lemma. If
you see this failure mode building `Canon`/`canonEquiv`, that is the fix:
name the fact under your own vocabulary before using it to build a
dependently-typed value, rather than debugging the `rw` call itself.

## Three elaboration gotchas, still live after eleven steps

- A bare `pure` inside `Tests/*.lean` or `Examples/*.lean` is ambiguous
  between `Graded.pure` and Mathlib's `Pure.pure` (and, once `Accum` is
  in scope, `Accum.pure` too) — write `Graded.pure`/`Accum.pure`
  explicitly there. Inside `namespace Graded` it resolves fine.
- `pure`/`Grade.bot` with no other `Graded`-typed argument nearby leaves
  `DecidableEq Err` stuck ("typeclass instance problem is stuck"). Fix
  with a full type ascription at the use site.
- `#guard`/`=` comparing two `Graded g α` (or `Accum g α`) values
  directly has not worked in any step. Route through a render-to-`String`
  function; every step so far has written its own. `Canon`/`Finset`
  equality, by contrast, decides fine directly (`Graded.Morphism`'s
  `#guard Grade.rename coarsen {...} = {...}` needed no render function)
  — the trouble is specific to the `Graded`/`Accum` inductives, not to
  every type in this codebase.
- `#guard` cannot carry a `/-- ... -/` doc comment; use a plain `--`.

## Do not use `git add -A` in the main checkout

The main checkout's working tree still has an uncommitted editorial pass
across all ten pre-[graded-morphism] letters under `blog/letters/`, made
by the repository's owner and deliberately left uncommitted (confirmed
still present after this step's merge). `git add -A` for your bookkeeping
commit in the main checkout would sweep those in. Stage your own files
by name instead. Inside your own worktree, `git add -A` is fine — the
edits are not there.

## `cast_ok`/`cast_err`/`cast_widen`/`cast_cast` live in `Graded/Monad.lean`/`Graded/Carrier.lean`

Not in `Carrier.lean` alone — `cast_cast` (composing two casts into one
along the transitive equality) is in `Carrier.lean`;
`cast_ok`/`cast_err`/`cast_widen` are in `Monad.lean`. Every law-heavy
step since [monad-laws] has used at least one of these.
