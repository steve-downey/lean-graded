# handoff → traverse-tuple

Goal and merge criterion: fixed by `step-traverse-tuple.md`.

## Dependencies are untouched

`traverse-list` added `Graded/Traverse.lean` only — a new file, new
definitions (`foldGrade`, `traverseRaw`, `traverse`) in the existing
`Graded` namespace, imported nowhere it wasn't asked for.
`Graded/Grade.lean` (`join_comm`, `join_assoc`, `join_idem`, `join_le`,
`bot_le`), `Graded/Applicative.lean` (`map2`, `ap`, `ap_ok_ok`,
`ap_ok_err`, `ap_err_left`), `Graded/Widen.lean` (`widen`, `fromEmpty`,
`widen_irrel`), `Graded/Monad.lean` (`pure`, `bind`), and
`Graded/Accum.lean` are byte-for-byte what [applicative-accumulation]
left them; nothing you cite from `docs/design.md#grade`/`#applicative`
has moved.

## `foldGrade` is not `joinAll` — don't reuse it

`Graded/Traverse.lean`'s `foldGrade (g : Grade Err) : List α → Grade Err`
folds one *fixed* grade `g` once per list element (`Grade.bot` at `[]`,
`Grade.join g (foldGrade g xs)` at `cons`) — it exists for the
uniform-element-grade case and takes a single `g`, not a list of grades.
Your `joinAll : List (Grade Err) → Grade Err := List.foldr Grade.join
Grade.bot` is a different function over a different shape of input (an
actual list of *distinct* grades, one per tuple slot) and has no shared
definition to extend — write it fresh in `Graded/Tuple.lean` as your step
file says. The two are conceptually siblings (both are "fold `Grade.join`
over a list, `Grade.bot` at the base") but not the same code and not
meant to become the same code.

## Proof pattern that worked for the analogous step (`sequence_cons`)

`traverse_cons` in `Graded/Traverse.lean` (`traverse f (x :: xs) = cast
(Grade.join_idem g) (map2 (· :: ·) (f x) (traverse f xs))`) is proved by
`cases` on `f x` then `cases` on the recursive call's result, each of the
three reachable branches closed by `simp only [widen, map2, map,
ap_ok_ok/ap_ok_err/ap_err_left, cast_ok/cast_err]` — reusing
`Graded.Applicative`'s existing reduction lemmas rather than deriving the
`bind`/`ap` unfolding from scratch. `sequence_cons` (`sequence (.cons x
xs) = map2 HList.cons x (sequence xs)`) is the same shape one level up —
expect the same three-way case split and the same reduction-lemma set to
close it, rather than reaching for `change`/manual unfolding (which cost
a rebuild in every earlier step that tried it first, per this step's own
inbound handoff).

## Two recurring elaboration gotchas, still live

- A bare `pure` inside `Tests/*.lean` or `Examples/*.lean` is ambiguous
  between `Graded.pure` and the generic `Pure.pure` — write `Graded.pure`
  explicitly at every use site there. Your `sequence_nil : sequence .nil
  = pure .nil` will hit this the moment `Tests/Tuple.lean` or
  `Examples/Validation.lean` writes out the expected value.
- `pure`/`Grade.bot` with no other `Graded`-typed argument nearby leaves
  `Err`'s `DecidableEq` instance stuck ("typeclass instance problem is
  stuck"). Fix: annotate explicitly, e.g. `(pure .nil : Graded
  (Grade.bot : Grade E) (HList []))`. Likely to bite `sequence_nil`-
  adjacent examples specifically.

## `#guard` on `Graded` equality still needs the render-to-`String` detour

Comparing two `Graded g α` values directly with `#guard`/`=` has not
worked in any step so far. Route your tuple `#guard`s (success case,
failure-in-the-middle-element case) through a render-style function to
`String`, same as `renderN`/`renderSum`/`renderPair` in
`Tests/Applicative.lean`/`Examples/Validation.lean` and this step's
`renderNats`. Pick a name that doesn't collide with `renderNats` (which
now renders `Graded ({E.parse} : Grade E) (List Nat)` in
`Examples/Validation.lean`) — your tuple result type is different anyway,
so a fresh render function is expected, not a reuse.

## Naming is already clash-free

This step's public name is `Graded.traverse`; yours is `sequence` per
your step file, so there is no name collision to worry about between the
`List` and tuple cases living in the same `Graded` namespace.

## Merge commit

`step/traverse-list` merged into `integration/lean-model` at
`2bf2a789762b491f8c69ddab464bce97099fedd6` (`--no-ff`).
`integration/lean-model` is GREEN (`make verify`, `make nosorry`, `make
letters` all exit 0) as of that commit.

## One finding not needed by this step, recorded for completeness

`foldGrade_le : foldGrade g xs ⊆ g` (bounded, any length) needed only
`Grade.join_le`/`Grade.bot_le`; `foldGrade_cons_ne_nil : xs ≠ [] →
foldGrade g xs = g` (exact, any nonempty length) needed `Grade.join_idem`
— the first theorem in the whole plan to need it. See
`docs/design.md#traverse` if you want the full writeup, but it has no
bearing on the tuple case: your `joinAll_perm` needs `join_comm` +
`join_assoc` and explicitly does **not** need idempotence (only
`joinAll_dedup` does), which is a different split over a different
structure.
