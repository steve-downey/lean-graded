# handoff → applicative-accumulation

Goal and merge criterion: fixed by `step-applicative-accumulation.md`.

## `docs/design.md#applicative` now has the exact `ap_flip` condition you need

The "same condition" your step asks you to confirm for `Accum.toGraded` is
stated, in `Graded/Applicative.lean`, as this hypothesis on `ap_flip`:

```lean
theorem ap_flip (f : Graded g (α → β)) (x : Graded h α)
    (honeok : (∃ f', f = Graded.ok f') ∨ (∃ a, x = Graded.ok a)) :
    ap f x = cast (Grade.join_comm h g) (apFlipped f x) := ...
```

"At most one side is an error" is spelled `(∃ f', f = .ok f') ∨ (∃ a, x =
.ok a)` — an `Or` of two existentials, not a boolean predicate — because
no `isOk`/`isErr` helper exists on `Graded` (deliberately not added; out
of that step's file scope). If `Accum.toGraded_grade`'s one-sided version
wants the same shape of hypothesis, match this rather than inventing a
new predicate; `rcases honeok with ⟨f', rfl⟩ | ⟨a, rfl⟩` is what
discharges it.

## The `ap` property table landed exactly at unit + associative — confirmed, not just predicted

All four laws (`ap_pure_id`, `ap_pure_pure`, `ap_interchange`, `ap_comp`)
needed only `Grade.bot_join`/`Grade.join_bot`/`Grade.join_assoc`.
`Grade.join_comm` appears exactly once in the whole module, in `ap_flip`,
required by comparing `ap`'s grade `join g h` against `apFlipped`'s `join
h g`. Your step's own prediction ("interchange needs the same as in
[applicative-from-monad]") should hold for `Accum.ap_interchange` too —
but see the next note for *how* to state it so that's actually true.

**The `ap_interchange` technique, if you need it again:** stating a law
as *two* casts landing at the same tidy grade — `cast (Grade.join_bot g)
(lhs) = cast (Grade.bot_join g) (rhs)`, both sides ending at plain `g` —
needs only the two separate unit lemmas. A single cast comparing `g ∪ ∅`
directly against `∅ ∪ g` would need `Grade.join_comm` instead. If
`Accum`'s interchange law has the same `g ∪ ∅` / `∅ ∪ g` shape, use the
two-cast phrasing to keep it comm-free, matching the finding above rather
than contradicting it by accident.

## Proof pattern that closed every `ap` law without hand-written `change` blocks

Reduction lemmas first, laws second. For each constructor combination of
`ap`'s two arguments, a small lemma like:

```lean
theorem ap_ok_ok (f' : α → β) (a : α) :
    ap (Graded.ok f' : Graded g (α → β)) (Graded.ok a : Graded h α) = Graded.ok (f' a) := by
  simp only [ap, bind, pure, widen]
  rw [cast_ok]
```

`simp only [<defName>, ...]` unfolds a `def` and performs the constructor
pattern-match reduction; you need **every** `def` the expression passes
through in the simp set (`ap`, `bind`, `widen`, `pure` as applicable) or
a `widen`/`bind` application is left stuck un-reduced. The final `rw
[cast_ok]`/`rw [cast_err]` (from `Graded.Monad`) closes the leftover
`cast`; for `.err` goals `rw` auto-closes via `rfl` afterward because the
membership-proof field is a `Prop` and Lean's proof irrelevance makes two
different proofs of the same membership defeq — you never need to prove
the two proof terms *equal*, just get both sides down to `Graded.err
<same e> _`. If `simp only [...]` reports "this simp argument is unused,"
remove it — the build must stay warning-free.

Once you have the reduction lemmas (`Accum.ap`'s equivalents — you'll
likely want cases for both-ok, both-err with concatenation, and one-err),
the four/five law proofs are `cases`+`simp only [reduction lemmas]`+one
`rw`, not manual unfolding. `ap_comp` (three nested `cases`, 8 leaves)
went through on the first attempt written this way — budget for it, but
it is not the multi-attempt slog the plan flagged it as.

## Two elaboration gotchas that cost a rebuild each

- `pure`/`Grade.bot` with no other `Graded`-typed argument nearby leaves
  `Err`'s `DecidableEq` instance stuck ("typeclass instance problem is
  stuck ... type argument to `DecidableEq` is a metavariable"). Fix:
  annotate explicitly, e.g. `(pure f : Graded (Grade.bot : Grade Err) (α
  → β))`, before Lean tries to resolve the instance.
- Inside `Tests/*.lean` (which `open Graded` and pull in Mathlib), a bare
  `pure` is ambiguous between `Graded.pure` and the generic `Pure.pure` —
  error "Ambiguous term `pure`". Write `Graded.pure` explicitly at every
  use site in test/example files (not needed inside `Graded/*.lean`
  itself, where there's no competing `pure` in scope).

## `#guard` on `Graded` equality: still routes through `String`

The `render`-to-`String` workaround from [monad-laws]'s handoff is now
used again in `Tests/Applicative.lean` (`renderN`) and
`Examples/Validation.lean` (`renderSum`) — copy that pattern for
`Accum`'s guards rather than comparing two `Accum g α` values directly.

## Merge commit

`step/applicative-from-monad` merged into `integration/lean-model` at
`1d9161dc0a941f3fefda2cc640fb9fa671817e86` (`--no-ff`).
`integration/lean-model` is GREEN (`make verify`, `make nosorry`, `make
letters` all exit 0) as of that commit. `seqLeft`/`seqRight` were **not**
added (nothing in this step needed them); `Graded/Applicative.lean` has
no trace of them if you were expecting to build on them.
