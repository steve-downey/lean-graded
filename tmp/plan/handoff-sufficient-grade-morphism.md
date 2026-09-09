# handoff → sufficient-grade-morphism

Goal and merge criterion: fixed by `step-sufficient-grade-morphism.md`.

## The tree you branch from

Twenty-two steps done and merged on `integration/lean-model`. `make all`
exits 0, tree clean, 183 theorems in the generated table (174 before this
leg; this leg added 9: `traverseK_irrel`, `traverseK_nil_eq_fromEmpty`,
`traverseK_map`, `traverseK_fromEmpty`, `traverseK_cons_ok_ok`,
`traverseK_cons_err_left`, `traverseK_cons_ok_err`, `traverseK_length`,
`traverse_eq_traverseK`). All nine cite no pomonoid property; all are on
`scripts/laws-inventory.py`'s `ALLOWLIST`, each with its own reason.

## What the traversal leg found, and what it means for a structure's
## field types rather than theorem statements

The fold disappeared entirely. `foldGrade`/`foldGrade_cons_ne_nil` (the
theorems that cost idempotence to compute and certify a traversal's exact
grade) have **no analogue** in `traverseK`'s world — not a cheaper one,
none. Every `traverseK_*` law cites zero pomonoid properties, confirming
[obligation-layering]'s classification of the five `Traverse.lean`
idempotence citations as canonicalization: about the union-graded
traversal's own grade-spelling, never about a value it picks.

**The one place idempotence still appears is the bridge**,
`traverse_eq_traverseK` (`traverse f xs = traverseK (Grade.le_refl' g) f
xs`), and only because `traverse_cons` itself computes through `Grade.join
g g` and identifies it with `g` on the union-graded side. `traverseK`'s
own side of that induction is `rfl` throughout. Your leg's own bridge
question (`GradedHom_eq_GradedHomK`, one-directional per your step file's
own prediction) has the same shape: expect any residual cast or property
citation to live entirely on the union-graded side of an equation, never
on the `K`-suffixed side, since nothing in this codebase's sufficient-grade
layer has yet needed a property to state its *own* half of anything.

## Which reduction lemmas generalise beyond `List`, since your leg has none

None of this leg's own lemmas are directly reusable — `traverseK_map`,
`traverseK_fromEmpty`, `traverseK_length`, and the three
`traverseK_cons_*` reduction lemmas are all stated over `List α` by
induction on `::`/`[]`, so there is nothing here for a structure with no
list in it to import by name.

What generalises is the *pattern*, already established before this leg by
`bindK`/`apK` and confirmed again here: a value threaded only as a `Prop`
(a `⊆` proof) is free by `rfl`, because Lean's proof irrelevance makes any
two proofs of the same membership or subset fact definitionally equal.
`traverseK_irrel` is this leg's own instance of that pattern
(`traverseK hg f xs = traverseK hg' f xs := rfl`, one witness, unlike
`bindK_irrel`'s two) and it is exactly the fact your `GradedHomK.hom_bindK`
field needs to be well-typed with no cast: once `gmap_mono` replaces
`gmap_join`/`gmap_bot`, both sides of `hom_bindK` land in `Graded (gmap k)
β` for the same reason `bindK`'s own two threaded proofs never needed
reconciling — there is no second expression for the target grade anywhere
for a homomorphism law to be needed to identify.

## `docs/design.md#traverse`

The new `### The sufficient-grade layer` subsection (added this leg) has
the full cast-count table and the bridge discussion above, if you want the
comparison method for your own `#morphisms` subsection's table.

## Live elaboration gotcha this leg hit, worth carrying forward

Reduction lemmas built by `rw [foo_cons, hfx, hxs]` do **not** auto-close
by `rfl` the way earlier `bindK`/`apK` reduction lemmas did when written as
a single `:= rfl` — `rw`'s trailing reflexivity check does not unfold a
`def` like `map2K`/`apK` to see the two sides agree. Append an explicit
`rfl` after the `rw` chain rather than assuming it closes on its own; this
cost three "unsolved goals" errors in this leg, all fixed the same way.

## Metrics schema

`verify_runs` / `edit_iterations` / `proof_attempts`, not `attempts`.
Timestamps to `/tmp`, never into the worktree.
