# step: sufficient-grade-applicative

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

Added 2026-09-08. **Gated on [sufficient-grade-bind]'s verdict.**

## Gate — read this before anything else

Your inbound handoff carries [sufficient-grade-bind]'s measured verdict on
whether the cast-free layer is worth extending. **If it says no, this step
does not run.** Do not execute it, do not mark the checklist, and do not
write a `blocked-` file — a negative verdict is a completed question, not a
failure. Append a `metrics.jsonl` row with `"outcome": "skipped"` and a
note naming the verdict, mark this line in `checklist.md` as
`- [~] N. [sufficient-grade-applicative] — not run: see
[sufficient-grade-bind]'s verdict`, and halt. Say so in your report.

If the verdict is yes, proceed.

## Why

This is where the cast burden is worst and where the payoff is largest.
`Comp.ap_interchange` in `Graded/ComposeApp.lean` carries **six casts in a
single statement**; `Comp.traverseComp_cons` has no content line at all,
only bookkeeping; `Graded/ComposeApp.lean` holds 6 of the model's 39
cast-in-statement theorems in 13 theorems. The two-coordinate composite is
exactly the case the integration review said [monad-laws]'s "tolerable"
verdict did not describe.

The applicative layer also has a shape the monad layer does not: `ap`
combines *two* independently graded values, so a sufficient grade `k` has
three subsumption obligations rather than two, and `Comp.ap` has two
coordinates each needing their own. Whether that stays free (by the proof
irrelevance `bindK_irrel` establishes) or starts costing at call sites is
the question this step answers for the harder case.

## What already exists

`docs/design.md#monad`'s `### The sufficient-grade layer` (`bindK`,
`pureK`, the cast-free laws, `bind_eq_bindK`, `bindK_irrel`, and the
measurement table), `#applicative` (`ap`, `apFlipped`, `map2`, the four
laws, `ap_flip`), `#compose` (`Comp`, `Comp.ap`, `flatten_ap`,
`Comp.grade_reassoc`).

## The change

Extend `Graded/Sufficient.lean` — do not create a second module.

- `apK`, `map2K` at a sufficient grade, defined **through `bindK`** so the
  "applicative is the monad's" story carries over. Reduction lemmas first.
- The four applicative laws, cast-free: `apK_pure_id`, `apK_pure_pure`,
  `apK_interchange`, `apK_comp`. Report the property each consumed.
  `apK_interchange` is the one to watch: at a common `k` the two-cast
  technique [applicative-from-monad] needed to keep it commutativity-free
  should become unnecessary, because both sides already land at `k`. **If
  it now needs `join_comm` where the union version did not, that is a
  finding against this design** — say so rather than absorbing it.
- `ap_eq_apK`, the bridge, tagged `/-- BRIDGE -/`.
- The composite: `CompK` or an equivalent at two sufficient grades, and
  `CompK.ap`, with the aim of stating `Comp.ap_interchange`'s analogue with
  **zero** casts against its current six. That number, before and after, is
  the headline measurement.
- `ap_flip`'s analogue. Note it needs `join_comm` in the union version *by
  construction* (comparing `join g h` against `join h g`); at a common `k`
  there is nothing to compare, so **expect commutativity to become
  unnecessary here**. If so, that is a substantive finding about where
  commutativity was really needed: not by the applicative, but by the
  choice to compute the grade exactly. Record it at `#applicative` and
  cross-reference [grade-obligations]' layering, which currently attributes
  commutativity to order-independence.

### Consumer

`Examples/Validation.lean`: `sumTwoK`, the independent-validation example
through `map2K`, `#guard`ed against `sumTwo`'s output. Leave `sumTwo` alone.

### Tests

Extend `Tests/Sufficient.lean`. Include one instance at a `k` strictly
larger than the join in *both* coordinates of the composite, so the
sufficient case is exercised in the two-coordinate setting.

### Living doc

`docs/design.md#applicative`: a `### The sufficient-grade layer`
subsection, the cast counts before and after, and the commutativity finding
if it materialises. Extend `#monad`'s measurement table rather than
starting a second one.

### Letter

`blog/letters/sufficient-grade-applicative.org`, **Letter 18**. Title from
what you actually find; if commutativity turns out to have been a cost of
exact grades rather than a requirement of the applicative, that is the
letter's subject and it is a better story than the cast counts. "Back in
C++": whether P3200's applicative needs `error_set` to be order-insensitive
at all, or only needs it because the return type is spelled as a union.

Add it to `blog/letters/index.org` after Letter 17.

## Declared file scope

`Graded/Sufficient.lean`, `Tests/Sufficient.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#applicative`, and
`#monad`'s table), `blog/letters/sufficient-grade-applicative.org`,
`blog/letters/index.org`. `Graded.lean`/`Tests.lean` only if a new import
is genuinely needed.

**No existing theorem's statement may change.** `Graded/Applicative.lean`
and `Graded/ComposeApp.lean` must not be edited. If you must, that is
`amendment-sufficient-grade-applicative.md` and a halt.

## Spot checks

```
git diff --name-only integration/lean-model~1...HEAD -- Graded/ | grep -v Sufficient   # empty
grep -c "cast" Graded/Sufficient.lean
grep -n "join_comm" Graded/Sufficient.lean     # ideally nothing; every hit needs justifying
grep -n "BRIDGE" Graded/Sufficient.lean        # two now
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-sufficient-grade-applicative -b step/sufficient-grade-applicative integration/lean-model
cd ../wt-sufficient-grade-applicative
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true
START=$(date +%s)
```

## Verify GREEN baseline / after

```
make all > /dev/null; echo all=$?      # must be 0, before and after
```
Regenerate `docs/laws.md` (`python3 scripts/laws-inventory.py`) and commit
it; this step adds theorems. Read `tail -n 20 build.log` only.

## Commit and merge back

```
git add -A
git commit -F- << 'MSG'
sufficient-grade-applicative: the cast-free applicative, and where commutativity really came from

Extends the sufficient-grade layer to ap, map2 and the two-coordinate
composite, where the cast burden was worst. If ap_flip's analogue needs no
commutativity at a common grade, then commutativity was a cost of
computing the grade exactly rather than a requirement of the applicative,
which changes what a grade must supply.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/sufficient-grade-applicative -m "merge step/sufficient-grade-applicative [sufficient-grade-applicative]"
```

Stage files **by name** in the main checkout.

## Record measurements

As in [sufficient-grade-bind], with the `verify_runs` / `edit_iterations` /
`proof_attempts` schema.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-sufficient-grade-applicative
git branch -d step/sufficient-grade-applicative
```

## Handoff

Mark `sufficient-grade-applicative` done in `tmp/plan/checklist.md`. There
is no next step file: whether `traverse`, `flatten`, `Comp` and `GradedHom`
follow is the open question
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope),
and its brief must be written from *your* measurements rather than guessed
now. Write `tmp/plan/handoff-cast-burden-migration.md` addressed to whoever
writes that brief: the cast counts before and after, whether the threaded
subsumption proofs stayed free, the commutativity finding, and which of the
four remaining structures you think is worth doing first and why.
