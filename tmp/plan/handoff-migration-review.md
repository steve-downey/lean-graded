# handoff → migration-review

Not a step. A scoped review, `model: opus`, of the three-leg
sufficient-grade migration just completed (checklist steps 19-24), the
same shape [integration-review] gave the first 18-step run but bounded to
this migration only. Do not re-review steps 1-18; [integration-review]
already did, and nothing in this migration touched their files.

## Scope: which steps, which "legs"

Six checklist entries, three conceptual legs:

- **Leg 1 — monad/applicative**: [sufficient-grade-bind] (19),
  [sufficient-grade-applicative] (20). Added `bindK`, `apK`/`map2K`/
  `apFlippedK`, `Comp.apK`.
- **Classification, between legs, load-bearing for both 2 and 3**:
  [obligation-layering] (21). Classified every `join_comm`/`join_idem`
  consumer in the *union-graded* model; found none operational. Every
  later leg's "no property needed" findings are checked against this
  step's table (`docs/design.md#obligations`), not asserted fresh each
  time — worth confirming the table is still accurate after legs 2 and 3
  rather than re-deriving it.
- **Leg 2 — traversal**: [sufficient-grade-traverse] (22). Added
  `traverseK`. The fold (`foldGrade`) has no analogue at all, not merely
  a cheaper one.
- **Leg 3 — structures**: [sufficient-grade-morphism] (23),
  [sufficient-grade-nested] (24, this step). Added `GradedHomK` (23) and
  `flattenK`/`Comp.pureK`/`Comp.map2K`/`traverseCompK`/`flatten_apK`
  (24). One leg because both subjects are "package a *structure*, not
  merely an operation," and 24's brief was written from 23's findings.

## Files touched, and what was never touched

Every leg is additive to **one file**: `Graded/Sufficient.lean` (57
theorems total across all six steps, **0** with a `cast` in their
statement — verify with `grep -c 'theorem'` against
`python3 scripts/laws-inventory.py --by-property` output, or just count
`docs/laws.json` entries with `"module": "Graded/Sufficient.lean"`).
Consumers: `Tests/Sufficient.lean`, `Examples/Validation.lean` (small,
additive reruns of existing consumers through the K-layer, `#guard`ed
identical). `docs/design.md`: sufficient-grade subsections under
`#monad`, `#applicative`, `#traverse`, `#morphisms`, `#compose`, plus
`#obligations` (leg-1/2 classification) and `#cast-burden-migration-scope`
(now CLOSED) and `#grade-join-strength` (still OPEN — see below).
`scripts/laws-inventory.py`'s `ALLOWLIST` (additions only, one entry per
theorem, each individually justified — spot-check a few rather than
trusting the count). `docs/laws.md`/`docs/laws.json` regenerated,
146 → 203 theorems. `blog/letters/sufficient-grade-{bind,applicative,
traverse,morphism,nested}.org` plus `obligation-layering.org`, and
`index.org`.

**Verify no operational module changed across all six steps**, not just
this one: `git diff --name-only <pre-leg-19-sha>...HEAD -- Graded/ | grep
-v Sufficient` should be empty. This step's own spot check only covered
step 24; the reviewer should widen it to the whole migration.

## Every bridge, and its direction — the one place to look hardest

Four **operation** bridges, all the same shape: instantiate the
sufficient-grade version at the exact union/computed grade, along the
same inclusions the union-graded operation itself uses, and recover it —
`rfl` in every constructor case, tagged `/-- BRIDGE -/`:
`bind_eq_bindK`, `ap_eq_apK`, `traverse_eq_traverseK` (pays
`Grade.join_idem` once, in the bridge's own induction, reconciling
`traverse`'s *own* two spellings of its grade — not a fact about
`traverseK`), `flatten_eq_flattenK` (this leg).

One **structure** bridge, a different shape entirely, and worth the
review's attention: `GradedHom.gmap_mono` derives *only* `GradedHomK`'s
`gmap_mono` field from `GradedHom`'s `gmap_join` field — not tagged
`BRIDGE`, deliberately, per [sufficient-grade-morphism]'s handoff. No
full `GradedHom → GradedHomK` structure map exists, and none in the
reverse direction either (the `constHomK` counter-instance shows why).
**Question for the review**: is a partial, one-directional bridge for
the one *record* in the model (vs. four full bidirectional-in-spirit
bridges for every *operation*) a stable pattern this migration
discovered, or a gap that a differently-shaped `GradedHom` could have
closed? The step files treat it as the former; it's worth a second look
with less investment in that conclusion.

## What's provisional or open in docs/design.md after this run

- **`cast-burden-migration-scope`: CLOSED** by this step, with a
  before/after summary table covering every structure in the model
  (`#cast-burden-migration-scope`). Check the table's own claims against
  the source rather than trusting the prose — it was assembled from
  `docs/laws.json`'s per-module counts plus each leg's own design.md
  subsection, not from a single mechanical query.
- **`grade-join-strength`: still OPEN.** Narrowed twice
  ([obligation-layering], then this step) but not settled: no leg in
  this migration ever built a sufficient-grade operation over the
  *abstract* `Pomonoid`/`Obligations.lean` framework (`Nat` included) —
  every leg is concrete, on `Grade Err`. Whether that abstract case is
  worth building is a separate, un-scoped question.
- **`Accum` row in the summary table**: explicitly "out of scope, still
  open" — never a candidate in the original question, flagged as a live
  thread for a possible fourth leg, not resolved here.

## What this review should produce

The same shape [integration-review] gave the first run: does the
two-layer-and-bridge design hold across all three legs without
exception (it claims to); is the `GradedHomK` bridge's asymmetry a
finding or a gap; is the cast-burden table's arithmetic right; anything
left provisional that a reader of `docs/design.md` would trip over.
