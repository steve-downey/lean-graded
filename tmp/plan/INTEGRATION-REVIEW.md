# Integration review — Lean model of graded Transpose

Run as a scoped `model: opus` consult after every implementation step in
`checklist.md` is checked. Not a Sonnet worker. Boot on
`tmp/plan/codebase-map.md` for the parts the run did not touch (it is a
map of the *pre-run* tree, stale by construction for everything the diff
covers); re-read from the tree for everything in
`git diff plan-base..integration/lean-model`. Read
`handoff-integration-review.md` from [blog-series-edit].

This is a judgment read for cross-step coherence, not a rerun of GREEN.
Then it is the sole consumer of `metrics.jsonl`. Write the review to
this file, below the line, replacing this brief.

## 1. First question: was the run actually fanned out?

Ask the orchestrator. There is no mechanical tell. If the steps ran
inline in one context, say so at the top of the review and **do not
promote `metrics.jsonl`**; the rows describe one session and would
corrupt every later calibration.

## 2. Cross-step coherence — what to look for

The plan's abstractions and the step that first consumed each:

| abstraction | introduced | first real consumer |
|---|---|---|
| `Grade` + named lemmas | grade-pomonoid | graded-carrier (bot), monad-laws (unit/assoc) |
| `Graded`, `cast`, `emptyEquiv` | graded-carrier | subsumption-widen, monad-laws |
| `widen`, `fromEmpty` | subsumption-widen | monad-laws (success path), traverse-list (empty) |
| `pure`/`bind` | monad-laws | applicative-from-monad |
| `ap`/`map2` | applicative-from-monad | traverse-list |
| `Accum` | applicative-accumulation | graded-morphism (optional) |
| `traverse`, `foldGrade` | traverse-list | compose-flatten, graded-morphism |
| `GList`/`joinAll` (and an `HList` if added to Prelude) | traverse-tuple | canonical-representation (`joinAll_perm`) |
| `flatten` | compose-flatten | — |
| `rename`, `GradedHom` | graded-morphism | — |
| `Canon` | canonical-representation | — |

Residue of a worked-around amendment, specifically:

- a second carrier other than `Accum` (which is planned and documented at
  `docs/design.md#applicative`); any `Graded'`, `GradedS`, a local
  `structure` wrapping `Graded`, or a second `widen`/`cast`;
- `cast` chains: if [monad-laws] recorded "casts dominated" at
  `docs/design.md#carrier` and no amendment followed, say whether the
  later proofs bear that out and whether the bind-at-sufficient-grade
  alternative should be a follow-up run;
- the **at-most-one-error condition**: it is predicted to appear in
  [applicative-from-monad] (`ap_flip`), [applicative-accumulation]
  (`toGraded`), and [compose-flatten] (`flatten_comm`). Check it is
  *stated once* as a named predicate and cited, or note that three
  steps spelled it three ways — that is exactly the drift a cleared
  worker cannot see;
- `PROPERTY:` tag discipline: every property lemma tagged; no later
  module re-proves a `Finset` fact inline instead of citing
  `Graded.Grade`; `docs/laws.md` from [oracle-export] agrees with a
  spot grep;
- a Mathlib lattice `instance` for `Grade` sneaking in (provisional
  decision in `#grade` says no);
- `Tests/`: any theorem instantiated only at `cast rfl` grades where the
  step asked for distinct concrete grades; any `example` that was
  commented out.

## 3. Context discipline held?

- Every `handoff-<slug>.md` ≤ ~150 lines and forward-only (grep for
  "previously", "in step", timings — all wrong contents).
- No step file grew a survey or a history section.
- `codebase-map.md` is referenced by no `step-*.md` and no handoff.
- `docs/design.md` is still by-anchor: every `##` from the baseline list
  exists exactly once, `#provisional-decisions` indexes every
  `Provisional.` mark in the file, and no section has become a log
  (dated entries, "update:" lines).
- The letters: `make letters` passes; no letter mentions agents, plans,
  tokens, or measurements (grep). Letters that contradict a later
  finding carry the bracketed note rather than a silent rewrite.

## 4. Metrics

Read `metrics.jsonl`. Produce per-step and whole-run: wall time, verify
wall time as a share, `log_bytes`, attempts, diff size, `out_of_scope`.
Name the hottest steps and say why — large diff, or cheap edit gated by
a long `lake build`. Those have opposite fixes: split the first; narrow
the verify target (`lake build Graded.<Module>` for the edit loop, full
`make verify` once) for the second. This run is the **baseline** —
there is no prior calibration — so the output is the floor
(`verify-floor` row) and the first sizing table, not a comparison.

Then promote: append the rows to `metrics/fanout-runs.jsonl` in the
repo (create it), tagged `run: lean-model-1`, `branch:
integration/lean-model`; commit. And write the one project memory entry
described in the plan-fanout template ("Where the measurements
accumulate"): what a step costs in this repo, which verify command
dominates, the edit/verify split, and every amendment that occurred
(which step's design, prompted by which consumer, at what cost). Update
in place on later runs; one entry, not one per run.

## 5. Findings for the C++ side

Last section, short: the list of things this run established that
should change P3200, the companion Monad paper, or the C++ repo — each
pointing at a theorem name and a letter. This is the one part of the
review Steve reads first; put it at the top of the written review even
though it is produced last.
