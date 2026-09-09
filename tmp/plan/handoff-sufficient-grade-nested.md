# handoff → sufficient-grade-nested

Goal and merge criterion: fixed by `step-sufficient-grade-nested.md`. This
is the last of three legs; you close
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope).

## The tree you branch from

Twenty-three steps done and merged on `integration/lean-model`. `make all`
exits 0, tree clean, 188 theorems in the generated table (183 before this
leg; this leg added 5: `rename_apK`, `rename_map2K`, `traverseK_rename`,
`GradedHom.gmap_mono`, `constHomK_not_gmap_bot`, all on
`scripts/laws-inventory.py`'s `ALLOWLIST` with individual reasons).
`Graded/Sufficient.lean` now also has a `section Morphism` (after `CompK`,
before `end Graded`) holding `GradedHomK`, `renameHomK`,
`rename_apK`/`rename_map2K`/`traverseK_rename`, `GradedHom.gmap_mono`, and
the counter-instance `constHomK`/`constHomK_not_gmap_bot`. `/-- BRIDGE
-/` count is still **3** (`bind_eq_bindK`, `ap_eq_apK`,
`traverse_eq_traverseK`) — this leg's own bridge (`GradedHom.gmap_mono`)
is deliberately untagged; see below for why, since your leg's
`flatten_eq_flattenK` is very likely a fourth genuine `BRIDGE` and should
be tagged.

## What the morphism leg found about bridges, and why it matters for yours

`GradedHom`/`GradedHomK` are two *structures* (records with obligations),
not two views of one *operation* the way `bind`/`bindK`,
`ap`/`apK`, and `traverse`/`traverseK` are. That distinction turned out to
matter: the three existing `BRIDGE` theorems each instantiate one
operation's sufficient grade at the other's computed one and close by
`rfl` — genuinely recovering one from the other at a specific point, in
both directions in spirit. The morphism leg's bridge does not have that
shape. `GradedHom.gmap_mono` derives `GradedHomK`'s `gmap_mono` obligation
from `GradedHom`'s `gmap_join` field — that is *all* that transfers, not
a full `GradedHom → GradedHomK` structure map, because building the rest
would need `GradedHom.hom` to commute with `widen` at an arbitrary
sufficient grade, and `widen` is a primitive of `Graded`
([carrier](../../docs/design.md#carrier)), not something `hom_bind`/
`hom_pure` pin down. An abstract `GradedHom` carries no such guarantee;
only a concrete function like `rename` (proved to satisfy `rename_widen`
separately) does.

**Your leg almost certainly does not hit this.** `flatten`/`Comp` are
operations, not records, so `flatten_eq_flattenK` should be the same
shape as the three existing bridges: instantiate `flattenK` at the
computed union, get `flatten` back by `rfl`, tag it `BRIDGE`, done. Read
the paragraph above as a warning sign only — if you find yourself writing
something structure-shaped for the nested carriers (you should not), the
same narrowing applies and is worth reporting the same way.

## What this means for your closing summary's "strict improvement or trade" column

The morphism leg's own row: `GradedHom`'s cast was not in a theorem
statement but in a **record field's type** (`hom_bind`'s signature
mentions `cast (gmap_join g h)` outright) — a different flavor of cast
burden than every other structure in the model, since it is a cost of
the *type* compiling at all, not of a proof obligation. `GradedHomK`
removes it by removing the obligation (`gmap_mono` alone) rather than by
threading a caller-supplied bound the way `bindK`/`apK`/`traverseK` do.
That makes it a **strict improvement**, not a trade: nothing was pushed
onto the caller to buy the cast's removal, because the caller-supplied
`⊆` proofs `hom_bindK` threads are the same shape `bindK` already needed,
not a new cost. Put `GradedHom`/`GradedHomK` in your table with that
distinction called out explicitly — "cast in field type" is worth its own
column note, separate from "cast in theorem statement."

## The pattern your own two structures should confirm or refute

Every leg so far, including this one, has found the same split: an
**order** half of an obligation (monotonicity, inclusion, "does the grade
get big enough") dissolves at a sufficient grade, while an **algebra**
half (which branch a value actually took) survives unchanged. Your step
file already predicts this for `flatten_ap`'s disjunctive hypothesis
("expect the grade half to dissolve and the value half to survive") —
that prediction is this same pattern, one structure further in. If
`flatten_comm` disappears entirely rather than surviving cast-free, that
is the pattern's most extreme case yet (an obligation with *no* algebra
half at all), not an exception to it.

## A tactic note worth carrying forward

`rw` with a lemma like `rename_err`/`rename_widen` that appears twice in
one goal with *different* implicit/proof arguments only rewrites the
occurrence it unifies against first, leaving the second untouched (`rw`
fixes the lemma's metavariables from its first match and only replaces
occurrences identical to that instantiation). `simp only [...]` with the
same lemma set does not have this problem — it rewrites every occurrence
regardless of differing implicit arguments and closes the remaining goal
via defeq (proof irrelevance) automatically. Reach for `simp only` over a
`rw` chain whenever the same reduction lemma needs to fire on both sides
of an equation with different proof terms; this cost several
"did not find an occurrence" errors this leg, all fixed the same way.

## Metrics schema

`verify_runs` / `edit_iterations` / `proof_attempts`, not `attempts`.
Timestamps to `/tmp`, never into the worktree.
