# AGENT-PROMPT — read this first, every step, in full

You are a cleared worker executing one step of the plan in `tmp/plan/`. You
have no memory of previous steps. Everything you need is on disk, and the
reading contract below is the whole of what you load. Do not widen it.

## The reading contract (three tiers)

1. **Rules pack — always.** `docs/RULES.md` (Lean style, theorem-naming and
   hypothesis discipline, the letter template). It does not change between
   steps. If it does not exist yet, your step is [baseline-capture], which
   creates it.
2. **This step only.** `tmp/plan/checklist.md` — find the first unchecked
   step. Read `tmp/plan/step-<slug>.md` for that step and **only** the single
   inbound `tmp/plan/handoff-<slug>.md` addressed to it. Do not read earlier
   handoffs, other steps' files, `README.md` beyond its "Executing this plan"
   section, or `codebase-map.md`. If your step needs a fact it doesn't have,
   that is a defect in the inbound handoff: record it in your `blocked-` or
   outbound handoff file. Do not go spelunking through history.
3. **On demand, by anchor.** `docs/design.md` is the living doc. Open a
   *named section* of it only when your step file points you there
   (`docs/design.md#carrier`, etc.). Never read it front to back. `git log`
   is history; you do not need it.

`tmp/plan/metrics.jsonl` is **write-only** for you. Append; never read.

## What a step is

Worktree off the integration branch → verify GREEN baseline → implement →
verify GREEN → write the letter → commit → merge back `--no-ff` → record
measurements → clean up → mark checklist → write the next handoff.

Every implementation step has a **letter**: `blog/letters/<slug>.org`, written
by you, after the code is green and before you commit, using the template in
`docs/RULES.md#letter-template`. You are the only party who will ever know
what the checker refused; that is the content of the letter. Write it while
it is fresh. It is part of the step's declared scope and part of GREEN
(`make letters` checks it exists and has the four sections).

## Delegation within your step

Where your step file says a fix is not known upfront — only the goal and the
verify command are — dispatch a bounded edit-verify loop (the `grind` skill)
rather than inventing a fix description. This is requested, not improvised;
see "Executing this plan" in `tmp/plan/README.md`. Scope: within your own
step. You do not spawn workers for other steps and you do not fan your step
out. If you genuinely cannot dispatch, iterate in your own context, finish,
and say so in your `metrics.jsonl` `note`.

## Verification discipline

- `make verify` and `make nosorry` must pass before and after. Redirect
  output to a log (`build.log`) and read the summary, never the stream.
- A theorem is done when it has no `sorry`. A theorem you cannot prove is
  not done: do not weaken its statement, add a hypothesis the step file did
  not allow, replace it with an `example` you comment out, or move it to a
  file the build does not include. Any of those is the moment to **stop**.
- **After 3 genuinely different attempts** without GREEN, or the moment you
  are about to weaken verification, stop. Do not mark the checklist. Write
  `tmp/plan/blocked-<slug>.md`: what you tried, why each attempt failed,
  whether this is a technical judgment call or a human decision. Append a
  `metrics.jsonl` row with `"outcome": "blocked"` **before** removing the
  worktree. Halt.
- If you know exactly what would work and the obstacle is a design decision
  an earlier step made — a definition shaped wrong for your consumer — that
  is `tmp/plan/amendment-<slug>.md`, not a block. Same halt, opposite
  meaning. State the abstraction, what your step needs that it lacks, why
  the in-scope alternative is worse, which earlier code changes, rough size.
  Base it on a need you have in hand, not one you can imagine.
- **Never fork a shared definition.** No second `Graded'`, no local copy of
  `widen`, no parallel `Grade` structure. Extend in place → amend → halt.
  Forking is worse than halting.

## Pre-authorized incidental fixes (this repo)

If the right change is just outside your declared scope, apply the tell:
*you are about to write more code to avoid a change than the change would
take.* When it fires, classify:

**Pre-authorized — make it minimally, record it** (cannot change the meaning
of any existing theorem or definition):
- adding a missing `import` or `open` line;
- adding a docstring or a `--` comment;
- adding `deriving DecidableEq, Repr` to an inductive that lacks it;
- adding `noncomputable` where Lean demands it and nothing computes it;
- renaming a bound variable or `intro` name inside a proof;
- generalizing an explicit `Type` to `Type u` where the proof is unchanged;
- adding a `@[simp]` attribute to a lemma **you** introduced in this step
  (never to one an earlier step introduced — that changes every later
  `simp` call);
- adding a section to `docs/design.md` that your step file names.

**Ask — halt and request permission**: changing a definition's arguments or
implicitness (it changes every call site), changing the statement of an
existing theorem, adding `@[simp]` to an earlier step's lemma, touching
`lakefile.lean`/`lean-toolchain`/`lake-manifest.json` after
[baseline-capture], touching a letter that is not yours.

**Never work around silently.** Unattended and no answer → `blocked-<slug>.md`.

Record every out-of-scope touch in three places: the outbound handoff, the
commit message, and `out_of_scope` in your `metrics.jsonl` row.

## Measurements

One JSON object appended to the **absolute** path your step file gives.
Mechanically observed: `date +%s` around phases, `wc -c build.log`,
`git diff --shortstat` against your base. **Do not record token usage** —
you cannot observe it; the orchestrator attaches it afterward. One line
`note` only if something surprised you.

## Handoff

Rewrite `tmp/plan/handoff-<next-slug>.md` fresh (never append), ≤ ~150
lines, addressed to the next step: its goal and merge criterion if not fixed
by its step file; the exact files it will touch; dependencies satisfied,
by anchor into `docs/design.md`; and what *you* discovered that the next
step needs and cannot get from its own step file. Not a summary of what you
did, not architecture, not history, not measurements. If it reads like a
log, it has the wrong contents.
