# handoff → cast-burden-migration-scope (open question, not a step)

[obligation-layering] is done and merged into `integration/lean-model`.
This replaces what [sufficient-grade-applicative] left here — read this
version, not any earlier one. It is not a step handoff; it is evidence
for whoever writes the next brief against
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope).

## The ordering recommendation carried forward unchanged

[sufficient-grade-applicative]'s recommendation stands: **`traverse`
next, then `flatten`, then the rest of `Comp`, then `GradedHom` last**
(cast-quantified *fields*, likely needs an amendment before a proof).
Nothing this step found changes that order. What it does change is how
cheap the first leg looks going in.

## `traverseK` exists now, and it is evidence, not the migration

This step added a bounded probe (`Graded/Sufficient.lean`): `traverseK`,
folding no grade at all, landing every element at a caller-supplied `k`
directly. `traverseK_cons` is `rfl`, cast-free, where `traverse_cons`
carries a `cast (Grade.join_idem g)`. **Do not read this as "traverse
migration done, just wire it up."** It is bounded on purpose: only the
uniform-`g`-over-`List` case, only two reduction lemmas, no
`traverse_map`/`traverse_length`/`traverse_fromEmpty`/`traverse_rename`
analogues, no interaction with `Comp.traverseComp_cons`. Extending it to
those is the actual [traverse] leg of this migration, not yet done.

**What it does establish, narrowly.** Length-independence is not a
*theorem* at a sufficient grade the way `foldGrade_cons_ne_nil` is one
for `traverse` — it is a property of `traverseK`'s *signature*
(`Graded k (List β)` for every list, before any theorem is stated). That
suggests the sufficient-grade traversal leg may be cheaper than
[sufficient-grade-applicative] guessed: no fold to reason about at all,
only reduction lemmas in the `apK`/`bindK` style. Confirm this by
actually building `traverse_map`/`traverse_length`'s analogues before
committing to it in a brief — one spike theorem proving `rfl` is not the
same claim as the whole leg being free.

**A caveat on my own evidence, so it isn't overstated a second time.**
An earlier spike (not mine, the orchestrator's, predating this step)
contained a `traverseK_grade` "theorem" that was `traverseK hg f xs =
traverseK hg f xs := rfl` — a tautology proving nothing about grades at
all. It is not in this step's output. Don't let a future brief cite it.

## The classification this step ran, and why it matters for scoping the rest

Every theorem in the model citing `Grade.join_comm`/`Grade.join_idem` (14
non-defining ones, mechanically enumerated via
`scripts/laws-inventory.py --by-property`, cross-checked against each
proof's actual case-split) is a canonicalization fact — a claim that two
expressions denote the same grade, or that a grade equals some fold —
never a claim about what an operation computes for a payload or error.
`docs/design.md#obligations` (revised) has the full table. Two
consequences for whoever writes the `flatten`/`Comp`/`GradedHom` briefs:

- **Do not expect a `join_comm`/`join_idem`-shaped cast to be "hard" in
  the operational sense.** Every migration so far (`bind`, `ap`, now the
  `traverseK` probe) has found these casts dissolve for the same reason:
  at a caller-nominated sufficient grade there is no second spelling to
  reconcile. `flatten_comm` (`Grade.join_comm`) and
  `Comp.traverseComp_cons`/`Comp.grade_reassoc` (`Grade.join_idem`/
  `join_comm`) are exactly this shape — budget them as "probably
  dissolves," not as a fixed cost to design around.
- **`GradedHom`'s cast-quantified fields are a different animal**, per
  [sufficient-grade-applicative]'s original flag, unaffected by this
  step's classification: those casts are in a *record's field types*,
  not a theorem's statement, so "does the property disappear at a
  sufficient grade" isn't even the right question there. Expect an
  amendment, not a proof, when that leg comes up.

## `grade-join-strength`: sharpened, not closed

`docs/design.md#grade-join-strength` now asks a narrower question than it
did: not "does the algebra force idempotence" (settled: no, `Nat` is the
witness) but "must a grade's C++ type promise canonical exact spelling —
order-independent and length-independent — for `traverse`'s signature to
be writable, or may a grade be a mere ordered monoid that simply doesn't
get `traverse`." This step's classification narrows the stakes (only
`traverse` is at issue; `bind`/`ap`/subsumption/morphisms need neither
property under either reading) but does not decide between them — that's
a decision about what P3200 should promise, not a fact the code
determines. If the `traverse` leg of this migration produces a grade that
is a `Pomonoid` but not an `IsCanonicalPomonoid` and still wants
`traverse`, that would be the concrete case that finally settles it one
way; watch for it.

## The restructured classes, if a future step needs to cite one

`Graded/Obligations.lean`: `Pomonoid` (operational, unchanged),
`IsCommPomonoid`/`IsIdemPomonoid` (independent siblings now, not nested —
`IsIdemPomonoid` no longer implies commutativity), `IsCanonicalPomonoid`
(both axioms, direct fields, the named bundle a real grade like `Grade
Err` inhabits). None of the three is used anywhere outside
`Graded/Obligations.lean`/`Tests/Obligations.lean` — this migration's
`traverse`/`flatten`/`Comp` legs operate on the concrete `Grade Err`
throughout and have no reason to reach for them.

## Files this migration will touch, by leg

- `traverse` leg: `Graded/Traverse.lean` (read only, for the shapes to
  mirror), `Graded/Sufficient.lean` (extend past `traverseK`'s two
  reduction lemmas), `Tests/Sufficient.lean`.
- `flatten` leg: `Graded/Compose.lean` (read only), `Graded/Sufficient.lean`.
- `Comp` leg: `Graded/ComposeApp.lean` (read only), `Graded/Sufficient.lean`.
- `GradedHom` leg: `Graded/Morphism.lean` — expect this one to need
  touching directly, hence the amendment expectation above.
