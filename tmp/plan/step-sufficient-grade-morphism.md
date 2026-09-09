# step: sufficient-grade-morphism

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

Second of three legs answering
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope).
Planned 2026-09-08.

## Why

Two earlier steps predicted this leg would need an amendment rather than a
proof, because `GradedHom`'s casts sit in a **record's field types** rather
than in theorem statements: `hom_bind`'s type mentions
`cast (gmap_join g h)`, so the cast is load-bearing for the structure to
typecheck at all, and "does the property dissolve at a sufficient grade"
looked like the wrong question.

**Both predictions were wrong, and the orchestrator checked before planning
this.** A sufficient-grade morphism states with no cast anywhere, and the
reason is the finding:

```lean
structure GradedHomK (Err Err' : Type u) [DecidableEq Err] [DecidableEq Err'] where
  gmap : Grade Err → Grade Err'
  gmap_mono : ∀ {g h : Grade Err}, g ⊆ h → gmap g ⊆ gmap h
  hom : ∀ {g : Grade Err} {α : Type u}, Graded g α → Graded (gmap g) α
  hom_bindK : ∀ {g h k : Grade Err} {α β : Type u} (hg : g ⊆ k) (hh : h ⊆ k)
      (x : Graded g α) (f : α → Graded h β),
      hom (bindK hg hh x f) = bindK (gmap_mono hg) (gmap_mono hh) (hom x) (fun a => hom (f a))
  hom_pureK : ∀ {k : Grade Err} {α : Type u} (a : α),
      hom (pureK a : Graded k α) = pureK a
```

`gmap_join` and `gmap_bot` — the *homomorphism* obligations — are gone as
fields, replaced by a single **monotonicity** obligation. Both sides of
`hom_bindK` land in `Graded (gmap k) β`, so there is nothing to re-type.

That revises [graded-morphism]'s account. It established that
`Finset.image` preserves union and ∅ unconditionally, for any `φ`, and
concluded that a grade morphism is a join-semilattice homomorphism. It
*does* preserve them. The operational obligation does not need it: **a
grade morphism need only be monotone.** Same order-in, algebra-out pattern
the `bind`, `ap` and traversal legs found, one level up — at the level of
what a *morphism between graded designs* must be, which is the part P3200
does not currently state at all.

**What the orchestrator verified, and what it did not.** The structure
declaration above elaborates. `renameHomK`'s `gmap_mono := Grade.rename_mono φ`
and `hom_pureK := rfl` both check. `hom_bindK`'s proof had one leaf
outstanding — the familiar shape where `bindK` must be reduced by its
`bindK_ok` lemma before casing on `f a`, because a lambda binder shadows
`a`. Treat the structure as established and that leaf as ordinary work.

## What already exists

`docs/design.md#morphisms` (`Grade.rename`, `rename_join`, `rename_bot`,
`rename_mono`, `rename_map`, `rename_pure`, `rename_bind`, `rename_widen`,
`rename_cast`, `traverse_rename`, `GradedHom`, `renameHom`, `Accum.rename`,
`Accum.rename_toGraded`), `#monad`'s and `#applicative`'s sufficient-grade
subsections, `#traverse`'s (added by the previous leg).
`Graded/Sufficient.lean` holds the cast-free layer and its bridges.

## The change

Extend `Graded/Sufficient.lean`.

- `GradedHomK` as above, and `renameHomK` instantiating it. Reduction
  lemmas first for the `hom_bindK` leaf.
- The `apK`/`map2K`/`traverseK` naturality analogues of `rename_ap`,
  `rename_map2` and `traverse_rename`, cast-free. `rename_cast` should have
  **no analogue at all** — there are no casts for it to commute with, which
  is worth saying rather than silently omitting.
- `GradedHom_eq_GradedHomK` or whatever bridge shape is actually available.
  **Be careful here and report honestly what you find**: bridging two
  *structures* is not the same as bridging two operations, and the fields
  differ (`gmap_join`/`gmap_bot` versus `gmap_mono`). A function from
  `GradedHom` to `GradedHomK` derives monotonicity from the homomorphism
  fields plus `join_eq_right_of_le` or similar; the converse probably does
  **not** exist, because monotone is strictly weaker. If the bridge is
  one-directional, that asymmetry *is* the result — it is the precise sense
  in which the union-graded design demands more of a morphism than the
  operations do. Do not manufacture a two-way bridge.
- Whether the weaker obligation admits a morphism the stronger one
  rejects: a monotone `gmap` that is not a join homomorphism, with a
  working `hom`. If you can build one, it is the counter-instance that
  makes the finding concrete rather than formal, in the way `Nat` did for
  [grade-obligations]. If you cannot, say so and say why — that is an
  honest weaker claim, and this project has taken several.

### Consumer

`Examples/Validation.lean`: the coarsening `E → E'` consumer from
[graded-morphism], rerun through `renameHomK`'s `hom`, `#guard`ed to render
identically. Leave the existing one alone.

### Tests

Extend `Tests/Obligations.lean` or `Tests/Sufficient.lean` as fits: the
structure's fields resolve, `renameHomK` typechecks at `E → E'`, a `#guard`
that computes.

### Living doc

`docs/design.md#morphisms`: a `### The sufficient-grade layer` subsection —
the structure, what obligations it dropped, the bridge's direction, and the
counter-instance or its absence. Revise the anchor's existing conclusion
about what a grade morphism must be so the two accounts do not stand side
by side as equals: the homomorphism facts remain true of `Finset.image` and
are no longer the obligation. Date it.

### Letter

`blog/letters/sufficient-grade-morphism.org`, **Letter 21**. This is the
best story of the three legs: two steps predicted a wall, the wall was a
field list, and moving one obligation from "preserves unions" to "preserves
order" dissolved it. "Back in C++": P3200 does not state what a
`transform_error`-shaped operation must satisfy; the answer is weaker than
anyone would have guessed, and weaker obligations admit more
implementations. Series register: addressee `"Steve,"`, signature
`"--SMD"`, **no em-dashes**. Add it to `blog/letters/index.org` after
Letter 20.

## Declared file scope

`Graded/Sufficient.lean`, `Tests/Sufficient.lean`, `Tests/Obligations.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#morphisms`),
`blog/letters/sufficient-grade-morphism.org`, `blog/letters/index.org`,
`scripts/laws-inventory.py` (`ALLOWLIST` only), `docs/laws.md` and
`docs/laws.json` (regenerated).

**`Graded/Morphism.lean` must not be edited.** Both prior steps expected
you would have to; the spike says you do not. If it turns out you must,
that is `amendment-sufficient-grade-morphism.md` and a halt — and it would
be a genuine finding, since it would mean the cast-free morphism cannot
coexist with the union-graded one.

## Spot checks

```
git diff --name-only integration/lean-model~1...HEAD -- Graded/ | grep -v Sufficient   # empty
grep -n "gmap_join\|gmap_bot" Graded/Sufficient.lean   # nothing: those obligations are gone
grep -n "cast" Graded/Sufficient.lean | grep -i hom     # nothing in the morphism section
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-sufficient-grade-morphism -b step/sufficient-grade-morphism integration/lean-model
cd ../wt-sufficient-grade-morphism
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true
START=$(date +%s)
```

## Verify GREEN baseline / after

```
make all > /dev/null; echo all=$?      # must be 0, before and after
```
Regenerate `docs/laws.md` and commit it. Read `tail -n 20 build.log` only.

## Commit and merge back

```
git add -A
git commit -F- << 'MSG'
sufficient-grade-morphism: a grade morphism need only be monotone

Two steps predicted GradedHom would need an amendment, because its casts
sit in field types rather than theorem statements. Replacing the
homomorphism obligations gmap_join and gmap_bot with a single monotonicity
obligation removes them: both sides of hom_bindK land in the same grade.
graded-morphism established that Finset.image preserves union and empty for
free and concluded that is what a grade morphism must be. It preserves
them; the operational obligation does not require it.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/sufficient-grade-morphism -m "merge step/sufficient-grade-morphism [sufficient-grade-morphism]"
```

Stage files **by name** in the main checkout.

## Record measurements

`verify_runs` / `edit_iterations` / `proof_attempts`, as in the preceding
legs.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-sufficient-grade-morphism
git branch -d step/sufficient-grade-morphism
```

## Handoff

Mark `sufficient-grade-morphism` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-sufficient-grade-nested.md`. Write
`tmp/plan/handoff-sufficient-grade-nested.md` fresh. That leg closes the
open question, so tell it what your bridge's direction implies for whether
the whole migration is a strict improvement or a trade.
