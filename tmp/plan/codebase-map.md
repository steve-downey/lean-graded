# codebase-map — transpose-lean

Base: **no commit yet**; the repository is created by [baseline-capture],
which tags the resulting state `plan-base`. Integration branch:
`integration/lean-model`. This map describes the tree *as the plan
intends it after baseline-capture*, because the consult that wrote it
had no tree to survey — a later consult must diff this against
`git ls-files` at `plan-base` before trusting it.

Consult-tier only. **Never on a worker's read path; no step file points
here.**

## Layout (post-baseline)

```
lakefile.lean            three lean_lib: Graded, Tests, Examples
lean-toolchain           whatever the Mathlib template pinned (see docs/design.md#toolchain)
lake-manifest.json       Mathlib pin; touching it after baseline is an "ask"
Graded.lean              root; imports every Graded/*.lean module
Graded/Prelude.lean      namespace + Finset import (+ HList if traverse-tuple adds one)
Graded/Grade.lean        grade-pomonoid: Grade, join, bot, PROPERTY-tagged lemmas
Graded/Carrier.lean      graded-carrier: Graded, map, emptyEquiv, cast
Graded/Widen.lean        subsumption-widen: widen, fromEmpty
Graded/Monad.lean        monad-laws: pure, bind, laws via cast
Graded/Applicative.lean  applicative-from-monad: ap, map2, ap_flip
Graded/Accum.lean        applicative-accumulation: Accum, toGraded, notMonad
Graded/Traverse.lean     traverse-list: foldGrade, traverseRaw, traverse
Graded/Tuple.lean        traverse-tuple: GList, joinAll, sequence
Graded/Compose.lean      compose-flatten: flatten and its laws
Graded/Morphism.lean     graded-morphism: rename, GradedHom, traverse naturality
Graded/Canonical.lean    canonical-representation: Canon, canonEquiv
Graded/ComposeApp.lean   compose-applicative: Comp, Comp.ap, traverseComp, flatten_ap
Graded/Ungraded.lean     ungraded-baseline: Fixed, pureF, bindF, apF, the Mathlib correspondence
Graded/Obligations.lean  grade-obligations: Pomonoid/IsCommPomonoid/IsIdemPomonoid, Finset and Nat instances
Tests.lean, Tests/*.lean one per module; examples at inductive E | parse | range | io
Examples.lean, Examples/Validation.lean   the single running consumer, grown by every step
Makefile                 verify | nosorry | letters | laws (laws added by oracle-export)
scripts/check-letters.sh, scripts/laws-inventory.py
docs/RULES.md            rules pack (tier 1)
docs/design.md           living doc (tier 3, by anchor); 14 anchors fixed at baseline
docs/laws.md, laws.json, probe-harness.md      oracle-export outputs
docs/allowed-axioms.md   empty list
blog/letters/<slug>.org  one letter per step; index.org + closing.org from blog-series-edit
metrics/fanout-runs.jsonl   created by the integration review
.github/workflows/ci.yml
```

## Build / test / lint entry points and cost

- `make verify` → `lake build`, all three libs. Cost after `lake exe cache
  get`: seconds to low minutes (measured in the `verify-floor` row).
  Without the cache: hours — treated as a block.
- `make nosorry` → grep. Trivial.
- `make letters` → shell. Trivial.
- `make laws` → python + diff. Trivial (exists after oracle-export).
- Per-module edit loop: `lake build Graded.<Module>` is the cheap verify
  for a `grind` loop; full `make verify` once at the end of a step.
- No coverage tool. No linter beyond Lean itself; Mathlib's linter is
  not wired in (a future run may add `lake env lean --run
  Mathlib/…/lint` — not this one).

## Principal abstractions and where they are defined

See the table in `INTEGRATION-REVIEW.md` §2 (kept there so the two do
not drift). The single most-shared definition is `Graded` in
`Carrier.lean`; the single most-cited file is `Grade.lean` (every law
proof cites its lemmas by name — this is by design and is what
`scripts/laws-inventory.py` mines).

## Seams the steps cut across

- `Examples/Validation.lean` is edited by nine steps in sequence. It is
  the intentional merge point; each step appends a stage or a `#guard`,
  never rewrites earlier ones (except monad-laws, which replaces the
  `REPLACED-BY: bind` block by design).
- `Graded.lean` and `Tests.lean` gain one `import` line per step.
- `docs/design.md` is edited by every step, each in its own anchor.
- `Graded/Prelude.lean` may be touched once by traverse-tuple (HList).

## Surprises worth not rediscovering

- The provisional `cast`-based law statement (`docs/design.md#carrier`)
  is the decision most likely to draw an amendment; the alternative is
  named there. If an amendment consult is convened for it, it
  re-decomposes monad-laws through compose-flatten and should not touch
  grade-pomonoid, graded-carrier, canonical-representation or the blog
  steps.
- `Accum` is planned, documented, and not a fork. Don't flag it.
- Letters are part of GREEN (`make letters`), so a step that is green on
  code but missing its letter is not done.
- The plan grew three steps after it started, all before oracle-export:
  [compose-applicative] (13), [ungraded-baseline] (14) and
  [grade-obligations] (15). The last two were added at the repository
  owner's request and are expected to carry two of the project's headline
  results — what grading costs over the ungraded laws, and what a grade
  must be for a design that does not want `error_set` to be its only
  possible grade. Neither refactors anything: the baseline fixes a grade
  inside the existing machinery, and the obligations step abstracts the
  grade algebra only, which is separable from the carrier.
- The plan grew one step after it started. [compose-applicative] was
  inserted at 13 (before oracle-export) on 2026-09-08, because
  [compose-flatten] tested a *flattened* composition law, refuted it, and
  the record briefly read as though graded traversable composition had
  failed — it had not been tested. `step-compose-flatten.md` carries a
  dated amendment saying so; the open question is
  `graded-traversable-composition` at `docs/design.md#compose`. Worth
  checking whether other steps make the same shape of substitution:
  naming the right structure and then testing a convenient one.
- The C++ side is **not** in this repository. Facts about it live only in
  `docs/design.md#cpp-counterpart`, written at baseline from the plan.
  If the C++ design moves, that section is the one to update, and the
  steps read it by anchor.
