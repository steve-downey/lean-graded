# Plan: a Lean 4 model of graded Transpose (grade = error_set)

Plan produced 2026-09-07 by a scoped planning consult (plan-fanout skill).
Target repository: a **new** Lean 4 project, working name `transpose-lean`
(rename at will; the plan never depends on the name). Integration branch:
`integration/lean-model`, created by [baseline-capture] off `main`.

## Executing this plan

**Sub-agent dispatch is the requested mechanism.** The user asked for this plan
by invoking the plan-fanout skill, whose stated purpose is a plan for cleared
sub-agents to execute. That request is recorded here so an orchestrator booting
on this file alone, without the conversation that asked for it, has it in hand.
A standing "don't call the Agent tool unless the user requested it" rule is
*satisfied* by this section, not overridden.

- One cleared worker per step, `model: sonnet`, explicit — never inherited.
- Each worker boots on `AGENT-PROMPT.md`, `checklist.md`, its own
  `step-<slug>.md`, and the single `handoff-<slug>.md` addressed to it. Nothing
  else on the mandatory read path.
- Amendments (`amendment-<slug>.md`) and the final integration review run as
  scoped `model: opus` consults that boot on `codebase-map.md`.
- **If you cannot dispatch sub-agents — permission denied, tool unavailable, a
  standing instruction you can't reconcile — halt and say so. Do not execute
  the steps inline.** An inline run looks successful and has none of the
  properties this plan exists for; its `metrics.jsonl` rows would poison the
  calibration. A halt is legible; an inline run is not.

## Strategy

The goal is a second implementation of the P3200/beman.transpose grading
design — grade pomonoid `error_set` (join-semilattice of error types), carrier
`expected<T, error_set<Es...>>`, bare `T` at grade ∅, subsumption by implicit
conversion, monad/applicative/traversable typeclass objects — written in Lean 4
so that every law is a theorem and every *hypothesis* a law needs is visible.
Alongside the code, an epistolary blog series (one letter per step, written by
the worker that did the step) for programmers who have never opened Lean.

Ordering follows "vertical slice, consumer early": the carrier gets a real
consumer (a two-stage validation example) in the same step it is defined, the
monad follows before any applicative machinery, and every later structure is
exercised by that same example. Facts that are settled once and read by many
steps live in `docs/design.md` (the living doc), referenced by anchor. Every
design decision the plan makes speculatively is marked provisional at its
anchor; a worker that finds one wrong writes an amendment, not a fork.

Reasons this plan is worth its ceremony rather than a single session: the
decomposition itself encodes the theory questions (which lemma needs
idempotence, whether an accumulating applicative can share the carrier,
whether ∅-grade is an `Equiv` or a definitional identity), and getting any of
those wrong early cascades into every proof after it.

## Baseline state

**No prior calibration exists for this repository** (it is greenfield), so
this run's step sizing is the baseline being measured. The integration review
should compare against nothing and instead establish the floor: what one step
costs once `lake build` is paid.

This consult could **not** run the verify command: the repository does not
exist yet, and the planning environment had no Lean toolchain or network
access to the Mathlib cache. Row zero of `metrics.jsonl` is therefore
appended by [baseline-capture], which is the step that creates the project
and times the first green build. Expect the first `lake build` after
`lake exe cache get` to be seconds-to-minutes; a cold Mathlib build without the
cache is hours and is a `blocked-baseline-capture.md`, not something to wait
out.

## Acceptance commands (orchestrator, post-merge, on the integration branch)

Run in this order; stop at the first failure. The worker's own GREEN was
pre-merge and in isolation; these check a state that did not exist when the
worker ran them.

| command | what it checks | cost | cadence |
|---|---|---|---|
| `make verify` | `lake build` of every module, output to `build.log`, summary read | cheap after cache (seconds to a few minutes) | per step |
| `make nosorry` | no `sorry`, `admit`, `native_decide`, or `axiom` outside `docs/allowed-axioms.md` | trivial | per step |
| `make letters` | every step slug marked done in `checklist.md` has `blog/letters/<slug>.org`, and each letter has the four required sections | trivial | per step |
| `git diff --name-only <base>..HEAD` vs the step's declared scope minus its `out_of_scope` | drift | trivial | per step |
| read the new/changed `Tests/*.lean` | weakened bar (a theorem restated with a stronger hypothesis than the step allowed, a `sorry` moved into a test, an `example` replaced by a comment) | small | per step |

There is no coverage tool for Lean proofs in this plan; "coverage" here is
`make nosorry` plus the theorem inventory that [oracle-export] produces.
Nothing is instrumented, so nothing is per-run only.

## Models

Implementation steps: `sonnet`. Integration review and any amendment consult:
`opus`. Do not upgrade a step to Opus because it looks hard — if it needs
judgment, that is `blocked-<slug>.md` and human review.

## File index

- `AGENT-PROMPT.md` — universal worker prompt; encodes the three-tier reading contract and this repo's pre-authorized incidental fixes.
- `checklist.md` — ordinal + slug per step; the integration review is its last line.
- `step-<slug>.md` — one self-contained brief per step.
- `handoff-<slug>.md` — written by the previous step, addressed to `<slug>`, consumed once. (`handoff-baseline-capture.md` is supplied by this plan.)
- `metrics.jsonl` — write-only for workers; read only by the integration review.
- `codebase-map.md` — consult-tier map of the tree; never on a worker's read path.
- `INTEGRATION-REVIEW.md` — brief for the final Opus consult.
- Living doc (in the repo, not here): `docs/design.md`, created by [baseline-capture]. Rules pack: `docs/RULES.md`, same step.
- Blog: `blog/letters/<slug>.org`, one per step; ordered and indexed by [blog-series-edit].

## Steps (reading order)

1. baseline-capture — create the project, rules pack, living doc, Makefile; time the first green build; letter 0 "why a C++ person is doing this in Lean".
2. grade-pomonoid — `Finset Err` as the grade; each pomonoid property its own named lemma.
3. graded-carrier — `Graded g α` holding one error whose type is in `g`; `Graded ∅ α ≃ α`; `map`; the two-stage validation example as first consumer.
4. subsumption-widen — `widen (g ⊆ g')`; identity, composition, naturality.
5. monad-laws — `pure`/`bind` with exact union grades; the three laws stated through `Graded.cast`; the example rewritten with `bind`.
6. applicative-from-monad — `ap`/`map2` derived from `bind`; applicative laws; the "instance is identical" claim checked.
7. applicative-accumulation — where an accumulating (Validation-style) instance can live; same grade, different values, not a monad.
8. traverse-list — `traverse` over `List`; grade independent of length, with idempotence as an explicit hypothesis; the empty case via `widen`.
9. traverse-tuple — heterogeneous sequence over an `HList` of differently-graded values; static join.
10. compose-flatten — nested carriers, the product grade, and the union-flattening law.
11. graded-morphism — grade-respecting morphisms (error renaming), naturality of `traverse`.
12. canonical-representation — `Finset Err` versus sorted duplicate-free lists; the Lean statement of "`error_set<A,B>` is the same type as `error_set<B,A>`".
13. compose-applicative — the composed applicative with the product grade `(g, h)` kept unflattened, and the classical composition law stated against it. Added 2026-09-08; see `docs/design.md#graded-traversable-composition`.
14. ungraded-baseline — the same laws at a single fixed grade, where every join collapses by idempotence and every cast becomes `rfl`; the ordinary laws with no grade arithmetic in their statements, plus the correspondence to Mathlib's `LawfulTraversable (Sum σ)`. Supplies the second column the property table needs: what a law costs at all, versus what grading adds. Added 2026-09-08.
15. grade-obligations — the obligations on a grade, in three layers (pomonoid / + commutative / + idempotent), with `Finset` satisfying all three and the naturals under `+` satisfying the first two but not the third, where the traversal grade grows with the list. Tests the `#cpp-counterpart` requirement that `error_set` not be the only possible grade. Added 2026-09-08.
16. oracle-export — the law inventory with hypotheses, as a table the C++ probe harness can run against.
17. blog-series-edit — order the letters, write the index and the closing letter, run the voice check if the skill is present.
18. Integration review (Opus).

## Follow-up run: the cast burden (planned 2026-09-08)

The integration review found that [monad-laws]'s "casts tolerable, not
dominating" verdict was right for one grade coordinate at step 5 and does
not describe the two-coordinate composite: 39 of 146 theorems carry a
`cast` in their *statement*, `Comp.ap_interchange` carries six in one, and
`GradedHom`'s fields are cast-quantified.

The fix is **not** the provisional note's "replace `bind` with a
sufficient-grade version" — that would remove the casts by modelling a
design P3200 does not have, since the C++ `bind` really does compute the
union grade. It is two layers and a bridge, verified before planning:
`bind x f = bindK (le_join_left g h) (le_join_right g h) x f` is `rfl`.

19. sufficient-grade-bind — `bindK` beside `bind`, the three monad laws
    cast-free, the bridge theorem, and the measurement that decides the
    rest. Its letter (17) is the post explaining the difficulty and the fix.
20. sufficient-grade-applicative — **gated on 19's verdict.** `apK`,
    `map2K` and the two-coordinate composite, where the burden is worst,
    and the question of whether commutativity was ever needed by the
    applicative or only by computing the grade exactly.

Everything beyond those two is the open question
`cast-burden-migration-scope` in `docs/design.md`, deliberately unplanned
until the measurements exist.
