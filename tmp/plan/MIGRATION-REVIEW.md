# Migration review — the sufficient-grade layer

Run as a scoped `model: opus` consult after checklist steps 19–24. Not a
Sonnet worker, and not a rerun of GREEN. Boot on
`tmp/plan/handoff-migration-review.md`, which is thorough and does most of
a brief's work; this file adds only what the orchestrator knows and what
the review must produce. Write your review into this file, below the line,
replacing this brief.

`tmp/plan/codebase-map.md` is consult-tier and stale by construction for
anything this migration touched. Re-read from the tree.

## Provenance: the run was fanned out, and some briefs came from spikes

Six cleared subagents, `model: sonnet` explicit, one per step, each booting
on `AGENT-PROMPT.md` + `docs/RULES.md` + its own `step-<slug>.md` + its
single inbound handoff and nothing else. None ran inline. None spawned
sub-agents; each ran its edit-verify loop in its own context under
AGENT-PROMPT's fallback and said so. So `metrics.jsonl` rows 20–25 describe
six separate contexts and may be promoted.

**Three of the six briefs were written from orchestrator spikes rather than
from a predecessor's findings, and a spike is weaker evidence than a step:
it establishes that something elaborates, not that it survives a full
build.** Treat these as claims to re-check, not as settled inputs:

- [sufficient-grade-bind] — `bindK`'s shape and the `bind_eq_bindK` bridge
  being `rfl` came from a spike. The worker confirmed both.
- [sufficient-grade-traverse] — `traverseK`'s shape came from a spike whose
  first version contained a tautological `traverseK_grade` theorem reading
  `x = x := rfl`. It is not on disk and must not be cited; the honest claim
  is that length-independence became a property of the signature.
- [sufficient-grade-morphism] — `GradedHomK`'s field list came from a spike
  that left one proof leaf open. Two earlier steps had predicted this leg
  needed an amendment; the spike said otherwise and the worker agreed.

## Orchestrator errors to assume rather than discover

Prose in this repo has been wrong about counts five times, three of them
mine, and every one was caught by checking the generated table instead of
another sentence. **Assume nothing in narrative text is right because it is
written down.** Specifically:

- I claimed `Comp.grade_reassoc` was "the second appearance of `join_comm`
  in the model". Six theorems consume it. Fixed at five sites in `94bd0b8`.
- I told a step file to expect four `/-- BRIDGE -/` tags when there were
  two; a worker recorded the discrepancy rather than adjusting code, which
  was correct.
- I measured "39 of 146 theorems carry a cast in their statement" with a
  scanner that cut statements at `:=` and so swallowed the proofs of
  equation-style theorems. The right figure is 38 of 146. Corrected in
  `docs/design.md` in `581da13`; the two `tmp/plan/` briefs still say 39
  **on purpose**, because they are the documents the workers received.

The same scanner bug made me doubt [sufficient-grade-nested]'s claim that
all 57 theorems in `Graded/Sufficient.lean` are cast-free in their
statements. The worker was right; I was wrong. Re-verify it your own way.

## Two things the inbound handoff gets slightly wrong

- It says every leg is "additive to **one file**, `Graded/Sufficient.lean`".
  [obligation-layering] (21) also restructured `Graded/Obligations.lean` —
  authorized, in its declared scope, and not an operational module by that
  step's own list. So "no *operational* module changed" holds; "one file"
  does not. Confirm the stronger claim yourself:
  `git diff --name-only 2c2e4dd..HEAD -- Graded/` should show exactly
  `Sufficient.lean` and `Obligations.lean` and nothing else.
- It asks you to widen the no-operational-module check to the whole
  migration. `2c2e4dd` is the pre-leg-19 baseline.

## A defect already fixed, mentioned so you do not re-find it

`metrics.jsonl`'s last row would not parse: a `printf`-written row used the
shell's `'\''` idiom to get an apostrophe into a Lean identifier and
produced an invalid `\'` JSON escape. Fixed in `8626f70`; all 25 rows now
parse. Note the pattern for your recommendations: every metrics row in this
repo is assembled by `printf` inside a shell command, which is also how an
empty `$START` once produced `wall_seconds: 1788879160`.

## What to produce

1. **Findings for the C++ side, at the top**, each pointing at a theorem
   name and a letter number. This is the section read first.
2. Does the two-layer-and-bridge design hold across all three legs without
   exception? It claims to.
3. **The `GradedHomK` bridge asymmetry**: four full operation bridges,
   one partial one-directional structure bridge, deliberately untagged.
   The step files treat that as a pattern the migration discovered. Decide
   with less investment in that conclusion whether it is a finding or a gap
   a differently-shaped `GradedHom` would have closed.
4. Is `#cast-burden-migration-scope`'s summary table's arithmetic right? It
   was assembled from per-module counts plus each leg's own subsection, not
   from one mechanical query.
5. `grade-join-strength` is still OPEN after two narrowings. Say whether
   that is right, and what the cheapest thing that would settle it is.
6. Metrics for steps 19–24: wall time, the edit/verify split, and what a
   leg costs in this repo now that the technique is routine. **Promote**
   the six rows to `metrics/fanout-runs.jsonl` tagged
   `run: lean-model-2`, `branch: integration/lean-model`, and commit.
7. **Do not write the project memory entry.** Produce its content in your
   report; memory is the orchestrator's to keep.

Also: is anything in `docs/design.md` now something a reader would trip
over — a superseded account left standing, an anchor that accumulated
instead of being revised, a provisional mark not in
`#provisional-decisions`? The first run's review found three such and they
were the most useful thing it produced.
