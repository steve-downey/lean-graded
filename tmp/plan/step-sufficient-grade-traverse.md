# step: sufficient-grade-traverse

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

First of three legs answering
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope).
Planned 2026-09-08.

## Why

`Graded/Traverse.lean` has 12 theorems, 2 carrying a cast in their
statement, and **5 of the model's 9 idempotence citations**:
`foldGrade_cons_ne_nil`, `traverse_cons`, `traverse_cons_err_left`,
`traverse_cons_ok_err`, `traverse_fromEmpty`. [obligation-layering]
classified every one as a canonicalization fact — idempotence appears only
in a cast target, never in the case split that picks the resulting value.

If that classification is right, the traversal leg should not merely lose
its casts: **the fold should disappear.** `foldGrade` exists to compute the
exact grade of a traversal, and `foldGrade_cons_ne_nil` exists to prove
that grade is `g`. At a caller-nominated sufficient grade there is nothing
to fold and nothing to prove: every element lands at `k` directly.

[obligation-layering] left a bounded probe on disk (`traverseK`,
`traverseK_nil`, `traverseK_cons`, both `rfl`) and was explicit that it is
**not** the migration: no `traverse_map`, `traverse_length`,
`traverse_fromEmpty` or `traverse_rename` analogues, and no interaction
with `Comp`. Its handoff asks the next brief to confirm the leg is cheap by
building those analogues rather than inferring it from one `rfl`. That is
this step.

## What already exists

`docs/design.md#traverse` (`foldGrade`, `foldGrade_le`,
`foldGrade_cons_ne_nil`, `traverse`, `traverse_nil`, `traverse_cons`,
`traverse_map`, `traverse_length`, the identity law), `#monad`'s and
`#applicative`'s `### The sufficient-grade layer` subsections, `#obligations`
(the classification table). `Graded/Sufficient.lean` holds `bindK`, `pureK`,
`apK`, `map2K`, `apFlippedK`, `traverseK` and its two reduction lemmas, and
three `/-- BRIDGE -/` theorems.

## The change

Extend `Graded/Sufficient.lean`. Do not create a module.

- Reduction lemmas for `traverseK` in the established style, before any
  law. Every previous leg that reached for `change`/manual unfolding first
  paid for it.
- **The analogues the handoff asks for**: `traverseK_map`,
  `traverseK_length`, the identity law, and `traverseK_fromEmpty` or
  whatever the ∅-grade case becomes when `widen`-along-`foldGrade_le` is no
  longer how the empty list is handled. Report the cast count for each
  against its union-graded original, and the property each consumed.
- `traverse_eq_traverseK`, the bridge, tagged `/-- BRIDGE -/`. This is the
  theorem that keeps `Graded/Traverse.lean`'s account of C++ `traverse`
  intact: the union-graded traversal is the sufficient-grade one at the
  fold. **If the bridge cannot be stated, that is the finding** — it would
  mean the two traversals are not the same operation, which is far more
  interesting than the cast counts, and it is a halt with an amendment
  rather than something to work around.
- `traverseK_irrel`, mirroring `bindK_irrel`: which `⊆` proof was threaded
  does not matter. Expect `rfl`.

**The claim to test, and to report either way.** `foldGrade` and
`foldGrade_cons_ne_nil` should have no analogue at all — not a cheaper one,
*none* — because the fold is what the exact grade cost and the sufficient
grade does not pay it. If you find yourself writing a `foldGradeK`, stop
and ask what it is for; if it turns out to be genuinely needed, say so,
because that would refute [obligation-layering]'s classification of the
five idempotence citations.

### Consumer

`Examples/Validation.lean`: `traverseK parseNat` over the same three inputs
`traverse parseNat` uses (`["1","2","3"]`, `["1","2","x"]`, `[]`), at a
literal `k`, `#guard`ed to render identically. Leave the existing traversal
consumer alone.

### Tests

Extend `Tests/Sufficient.lean`: each new law at `E`; one instance at a `k`
strictly larger than the element grade; a `#guard` that computes.

### Living doc

`docs/design.md#traverse`: a `### The sufficient-grade layer` subsection —
the definition, the analogues with their cast counts, the bridge, and
whether the fold disappeared. If it did, say plainly that
`foldGrade`/`foldGrade_cons_ne_nil` are artifacts of exact grading, and
cross-reference [obligation-layering]'s classification.

### Letter

`blog/letters/sufficient-grade-traverse.org`, **Letter 20**. The story for
a C++ reader is the one thing this leg has that the earlier two did not:
not "the noise went away" but "a whole function and its theorem turned out
to exist only to compute something nobody needed to compute." `foldGrade`
is the most C++-legible thing in the model, because it is what a compiler
would have to do to spell the return type; showing it evaporate when the
caller nominates the grade is the letter. Series register: addressee
`"Steve,"`, signature `"--SMD"`, **no em-dashes**. Add it to
`blog/letters/index.org` after Letter 19.

## Declared file scope

`Graded/Sufficient.lean`, `Tests/Sufficient.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#traverse`),
`blog/letters/sufficient-grade-traverse.org`, `blog/letters/index.org`,
`scripts/laws-inventory.py` (`ALLOWLIST` entries only), `docs/laws.md` and
`docs/laws.json` (regenerated).

**`Graded/Traverse.lean` must not be edited**, nor any other operational
module. You are reading it for the shapes to mirror. If you must edit it,
that is `amendment-sufficient-grade-traverse.md` and a halt.

## Spot checks

```
git diff --name-only integration/lean-model~1...HEAD -- Graded/ | grep -v Sufficient   # empty
grep -c "foldGradeK" Graded/Sufficient.lean          # 0 expected; any hit needs justifying
grep -n "join_idem" Graded/Sufficient.lean           # the leg should add none
grep -c "BRIDGE" Graded/Sufficient.lean              # 4 now
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-sufficient-grade-traverse -b step/sufficient-grade-traverse integration/lean-model
cd ../wt-sufficient-grade-traverse
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true
START=$(date +%s)
```

## Verify GREEN baseline / after

```
make all > /dev/null; echo all=$?      # must be 0, before and after
```
`make laws` goes red until you run `python3 scripts/laws-inventory.py` and
commit the result. Read `tail -n 20 build.log` only.

## Commit and merge back

```
git add -A
git commit -F- << 'MSG'
sufficient-grade-traverse: the fold was the cost, not the casts

foldGrade exists to compute a traversal's exact grade and
foldGrade_cons_ne_nil to prove it equals g, at the price of idempotence.
At a caller-nominated sufficient grade there is nothing to fold: every
element lands at k directly, length-independence is a property of the
signature, and five of the model's nine idempotence citations have no
analogue to need. traverse_eq_traverseK keeps the union-graded account of
C++ traverse intact beside it.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/sufficient-grade-traverse -m "merge step/sufficient-grade-traverse [sufficient-grade-traverse]"
```

Rewrite that message if the fold did not disappear. Stage files **by name**
in the main checkout.

## Record measurements

`verify_runs` / `edit_iterations` / `proof_attempts` schema, appended to
`/home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl`. Do not emit
`attempts`. Write timestamps to `/tmp`, not into the worktree.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-sufficient-grade-traverse
git branch -d step/sufficient-grade-traverse
```

## Handoff

Mark `sufficient-grade-traverse` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-sufficient-grade-morphism.md`. Write
`tmp/plan/handoff-sufficient-grade-morphism.md` fresh, per the contract in
`AGENT-PROMPT.md`. That leg touches a *structure*'s field types rather than
theorem statements, so tell it which of your reduction lemmas generalise and
which were list-specific.
