# step: obligation-layering

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

Added 2026-09-08, after [sufficient-grade-applicative].

## Why

[grade-obligations] answered "what must a grade be" with three layers: a
pomonoid carries the monad, applicative, subsumption and morphism laws;
commutativity adds order-independence; idempotence adds length-independence.
That was the honest reading of the evidence available at step 15.

[sufficient-grade-applicative] then changed the evidence. `ap_flip` needs
`Grade.join_comm` *by construction*, comparing `ap`'s grade `join g h`
against `apFlipped`'s `join h g`. Its cast-free analogue `apK_flip` needs
**no pomonoid property at all** — confirmed in the generated table, not
asserted — because at a common sufficient grade both sides already land in
`Graded k β` and there is nothing to compare. So commutativity was not a
requirement of the applicative. It was the price of spelling the result
grade as an exact canonical union.

That suggests a sharper account, and this step exists to establish or
refute it:

> **Hypothesis.** Every consumer of `join_comm` and `join_idem` in the
> model is a *canonicalization* fact — a claim that two spellings of the
> same grade are the same grade, or that a grade is exactly some fold.
> No *operational* law (monad, applicative, traversal, subsumption,
> morphism) needs either. The operational obligation on a grade is exactly
> the pomonoid: associative, unital, ordered, monotone.

If it holds, the three-layer account is wrong in an interesting way: the
second and third layers are not "more grade" but "the cost of canonical
exact spelling", and P3200 needs `error_set` to be a semilattice because
of what its *type* promises, not because of what its operations do. If it
fails, the counterexample is a single operational law that genuinely needs
commutativity or idempotence, and that is a better result than a third
confirmation.

## What already exists

`docs/design.md#obligations` (the three classes and the `Nat`
counter-instance), `#monad`'s `### The sufficient-grade layer`,
`#applicative`'s equivalent, `#traverse`, `#grade`, `docs/laws.md` and
`docs/laws.json` (172 theorems, generated), and the open question
[grade-join-strength](../../docs/design.md#grade-join-strength).

## Established before this step — reproduce, do not re-derive

The orchestrator verified two things by building them.

**1. The three classes are used nowhere outside their own module.**
`grep` over `Graded/`, `Tests/`, `Examples/` finds `Pomonoid`,
`IsCommPomonoid`, `IsIdemPomonoid` only in `Graded/Obligations.lean` and
`Tests/Obligations.lean`. Restructuring them therefore breaks nothing, and
you do not need an amendment to change their shape.

**2. At a sufficient grade, traversal needs no idempotence.** This spike
elaborates and every theorem in it closes by `rfl`:

```lean
def traverseK (hg : g ⊆ k) (f : α → Graded g β) : List α → Graded k (List β)
  | []      => pureK []
  | x :: xs => map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x) (traverseK hg f xs)

theorem traverseK_cons (hg : g ⊆ k) (f : α → Graded g β) (x : α) (xs : List α) :
    traverseK hg f (x :: xs)
      = map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x) (traverseK hg f xs) := rfl

theorem traverseK_nil (hg : g ⊆ k) (f : α → Graded g β) :
    traverseK hg f ([] : List α) = pureK [] := rfl
```

Compare `Graded.traverse_cons`, which carries `cast (Grade.join_idem g)`,
and `Graded.foldGrade_cons_ne_nil`, which needs `join_idem` plus
`join_bot` to prove the grade equals `g` for a nonempty list.

**Read the caveat, because the spike overstated itself once.** The
orchestrator's version also contained a `traverseK_grade` "theorem" that
was `traverseK hg f xs = traverseK hg f xs := rfl` — a tautology proving
nothing. The real evidence is narrower and you should present it as such:
length-independence stops being a *theorem* and becomes a property of the
*signature*, since the result type is `Graded k (List β)` for every list;
and `traverseK_cons` is cast-free where `traverse_cons` is not. Do not
restate the tautology.

This probe is **not** the traversal migration. That belongs to
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope).
You are adding only what the layering question needs: `traverseK`, the two
`rfl` laws above, and enough of a test to show it computes.

## The change

### 1. The mechanical re-derivation

From `docs/laws.json`, produce the current property-to-law map. Do not
hand-copy it from any prose in `docs/design.md`: two earlier steps'
narrative disagreed with their own generated tables, and one repeated a
wrong count four lines from the correct one. If you want a script, extend
`scripts/laws-inventory.py` with a `--by-property` reporting mode rather
than writing a second parser.

### 2. The classification, which is the step's real work

For **every** theorem citing `commutative` or `idempotent`, classify it as
*operational* (a law about what `bind`/`ap`/`traverse`/`widen`/`rename`
do to values) or *canonicalization* (a claim relating two spellings of a
grade, or asserting a grade is exactly some fold). Record the verdict per
theorem in a table, with a one-clause reason each. The current consumers
are, by module: `Applicative` (`ap_flip`), `Compose` (`flatten_comm`),
`ComposeApp` (`Comp.grade_reassoc`, `Comp.traverseComp_cons`), `Traverse`
(`foldGrade_cons_ne_nil`, `traverse_cons` and its two error
decompositions, `traverse_fromEmpty`), `Tuple` (`joinAll_perm`,
`join_mem_eq`), `Obligations` (`join_le`, `foldG_cons_ne_nil`,
`joinAllG_perm`), and `Grade` itself (the defining lemmas, which classify
as neither).

**A single operational counterexample refutes the hypothesis and is the
result.** Do not stretch a classification to make the hypothesis come out
right; if a law is genuinely about values and genuinely needs
commutativity, say so and the restructure below does not happen.

### 3. The restructure, if the hypothesis holds

Replace the `IsCommPomonoid` / `IsIdemPomonoid` tower with a shape named
for what it buys. A single mixin carrying both axioms, named for canonical
spelling rather than for its axioms, is the obvious candidate — but the
naming and the split are yours to choose and to justify at the anchor.
Keep `Pomonoid` as the operational obligation, keep the `Finset` and `Nat`
instances working, and keep every existing theorem in `Obligations.lean`
provable — if a restructure would require weakening one, stop and say so
rather than weakening it.

Whatever you choose, the field names must still match the corresponding
lemma names in `Graded/Grade.lean`, so [oracle-export]'s grep sees one
vocabulary.

### 4. [grade-join-strength]

The open question asks whether a grade's `join` must be a least upper
bound, and notes that `join_le` plus antisymmetry proves `join_idem`. This
step's hypothesis reframes it: if the operational layer never needs a LUB,
the question stops being about the algebra and becomes "must the grade be
canonically spelled?", which is a question about the C++ type. **Update
that question in place** with the reframing, and close it only if your
classification actually settles it. If it does not, say what would.

### Consumer

None. `Examples/Validation.lean` is not in scope; this step is about
obligations, not about a new operation. Do not add one.

### Tests

Extend `Tests/Obligations.lean` for the restructured classes, and add the
`traverseK` probe's own test: a `#guard` that it computes at a concrete
`k` strictly larger than the element grade.

### Living doc

`docs/design.md#obligations`, revised **in place**: the classification
table, the restructured obligation, and what changed from
[grade-obligations]' three-layer account and why. Do not add a new
top-level anchor, and do not leave the old account standing beside the new
one as though both were current — supersede it, and date the change.

### Letter

`blog/letters/obligation-layering.org`, **Letter 19**. Title from what you
find. If the hypothesis holds, the story for a C++ reader is that
`error_set` has to be a semilattice because of a promise its *type* makes,
not because `and_then` needs it — and the evidence is that the same
operations, asked to land in a grade the caller nominates, need neither
commutativity nor idempotence. Series register: addressee `"Steve,"`,
signature `"--SMD"`, **no em-dashes**. Add it to `blog/letters/index.org`
after Letter 18.

## Declared file scope

`Graded/Obligations.lean`, `Graded/Sufficient.lean` (the `traverseK` probe
only), `Tests/Obligations.lean`, `docs/design.md` (`#obligations` and
`#grade-join-strength`), `blog/letters/obligation-layering.org`,
`blog/letters/index.org`, `scripts/laws-inventory.py` (a reporting mode
and any `ALLOWLIST` entries your new lemmas need), `docs/laws.md` and
`docs/laws.json` (regenerated). `Graded.lean`/`Tests.lean` only if a new
import is genuinely needed.

**No operational module may change**: not `Grade.lean`, `Carrier.lean`,
`Widen.lean`, `Monad.lean`, `Applicative.lean`, `Accum.lean`,
`Traverse.lean`, `Tuple.lean`, `Compose.lean`, `ComposeApp.lean`,
`Morphism.lean`, `Canonical.lean`, `Ungraded.lean`. The classification is
a reading of them, not an edit to them. If it turns out you must edit one,
that is `amendment-obligation-layering.md` and a halt.

## Spot checks

```
git diff --name-only integration/lean-model~1...HEAD -- Graded/ | grep -vE 'Obligations|Sufficient'   # empty
grep -n "join_comm\|join_idem" Graded/Sufficient.lean    # the probe must add none
grep -c "^| " docs/design.md                              # the classification table exists
grep -n "Status:" docs/design.md                          # grade-join-strength updated
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-obligation-layering -b step/obligation-layering integration/lean-model
cd ../wt-obligation-layering
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true
START=$(date +%s)
```

## Verify GREEN baseline / after

```
make all > /dev/null; echo all=$?      # must be 0, before and after
```
`make laws` goes red until you regenerate: run
`python3 scripts/laws-inventory.py` and commit the result. Read
`tail -n 20 build.log` only.

## Commit and merge back

```
git add -A
git commit -F- << 'MSG'
obligation-layering: commutativity and idempotence are canonicalization costs, not operational ones

grade-obligations read the evidence as three layers of grade. The
sufficient-grade layer changed the evidence: the same operations, asked to
land in a grade the caller nominates, need neither commutativity nor
idempotence. Every consumer of both is a claim about grade spelling rather
than about what an operation does to values, so the operational obligation
is exactly the pomonoid and the rest is the price of canonical exact
grades.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/obligation-layering -m "merge step/obligation-layering [obligation-layering]"
```

If the hypothesis is refuted, rewrite that message to say what you found;
the commit must describe the step's actual result.

Stage files **by name** in the main checkout.

## Record measurements

As in the two preceding steps, with the `verify_runs` / `edit_iterations` /
`proof_attempts` schema. Do not emit `attempts`.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-obligation-layering
git branch -d step/obligation-layering
```

## Handoff

Mark `obligation-layering` done in `tmp/plan/checklist.md`. There is no
next step file. Write `tmp/plan/handoff-cast-burden-migration.md` **fresh,
replacing what [sufficient-grade-applicative] left there** — it is
addressed to the same reader, whoever writes the brief for
[cast-burden-migration-scope], and your classification changes what that
brief should say. Carry forward: the prior step's ordering recommendation
(`traverse`, then `flatten`, then the rest of `Comp`, then `GradedHom`
last because its cast-quantified fields probably need an amendment), your
own classification, whether `traverseK` makes the traversal migration
cheaper than that ordering assumed, and whether [grade-join-strength] is
now closed or merely sharpened.
