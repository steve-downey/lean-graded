# handoff → traverse-list

Goal and merge criterion: fixed by `step-traverse-list.md`.

## Dependencies are untouched

`applicative-accumulation` added `Graded/Accum.lean` only — a new file,
new namespace `Graded.Accum`, imported nowhere it wasn't asked for.
`Graded/Applicative.lean` (`map2`, `ap`, `pure`), `Graded/Widen.lean`
(`widen`, `fromEmpty`), `Graded/Monad.lean` (`bind`, `pure`), and
`Graded/Grade.lean` (`join_idem`, `join_le`, `bot_le`, `bot_join`) are
byte-for-byte what [applicative-from-monad] left them; nothing you cite
from `docs/design.md#applicative`/`#subsumption`/`#grade` has moved.

## Two recurring elaboration gotchas, still live

- A bare `pure` inside `Tests/*.lean` or `Examples/*.lean` (both `open
  Graded` and pull in Mathlib) is ambiguous between `Graded.pure` and the
  generic `Pure.pure` — "Ambiguous term `pure`". Write `Graded.pure`
  explicitly at every use site in test/example files. Your `traverseRaw`'s
  nil case is `pure []`; inside `Graded/Traverse.lean` itself this is fine
  (no competing `pure` in scope), but the moment `Tests/Traverse.lean` or
  `Examples/Validation.lean` writes out an expected value at grade `∅`
  using `pure`/`fromEmpty`, expect this error and use `Graded.pure`.
- `pure`/`Grade.bot` with no other `Graded`-typed argument nearby leaves
  `Err`'s `DecidableEq` instance stuck ("typeclass instance problem is
  stuck ... metavariable"). Fix: annotate explicitly, e.g. `(pure [] :
  Graded (Grade.bot : Grade E) (List Nat))`. Likely to bite
  `foldGrade_nil`/`traverse_nil`-adjacent examples specifically, since
  those are the ones that mention grade `∅` with nothing else around to
  pin `Err`.

## `#guard` on `Graded` equality still needs the `String` detour

Comparing two `Graded g α` values directly with `#guard`/`=` has not
worked in any step so far; every consumer routes through a `render`-style
function to `String` first (see `renderN`/`renderSum` in
`Tests/Applicative.lean`/`Examples/Validation.lean`, `renderErrs` in this
step's `Examples/Validation.lean` addition). Do the same for
`traverse`'s `#guard`s on `["1","2","x"]`/`["1","2","3"]`.

## Proof pattern for the recursive laws

`traverse_cons`/`traverse_map`/the identity law are all "induct on the
list, `cases`/`simp only` the base and step" shaped, same as
`Graded.Applicative`'s and `Graded.Accum`'s law proofs. What worked both
times: prove small reduction lemmas for how `traverseRaw`/`foldGrade`
compute on `[]` and `x :: xs` first (each closes by `rfl` or a one-line
`cases`), then write the real theorems as `induction xs with | nil => ...
| cons x xs ih => simp only [<reduction lemmas>, ih]`. Reaching for
`change`/manual unfolding first cost a rebuild in every earlier step that
tried it before falling back to this.

## Merge commit

`step/applicative-accumulation` merged into `integration/lean-model` at
`3bc493d` (`--no-ff`). `integration/lean-model` is GREEN (`make verify`,
`make nosorry`, `make letters` all exit 0) as of that commit.

## One finding not needed by this step, recorded for completeness

`Accum.toGraded_grade` (the accumulating carrier's own applicative,
unrelated to `List`) turned out to hold *unconditionally*, not only under
the one-sided hypothesis the step predicted — see
`docs/design.md#applicative` if you're curious, but it has no bearing on
`List`-shaped traversal.
