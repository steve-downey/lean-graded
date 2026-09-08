# step: blog-series-edit

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

Each letter was written by the worker who did the step, when it knew
what the checker refused. That gives sixteen honest letters and no
series: no consistent addressee voice, no cross-references, no arc, no
index, and possibly two letters that explain `DecidableEq` from
scratch. This step turns them into a series for a Lean-naive reader
without rewriting their substance — it is the one step allowed to read
every letter, once, as a bounded exception like the integration review.

## What already exists

`blog/letters/*.org` (one per implementation step);
`docs/design.md#blog-series` (addressee, **decided** — see step 1);
`docs/design.md#laws-inventory` (for the closing letter).

## The change

1. Read all letters once. The addressee is **already decided and already
   applied**: `"Steve,"` with the signature `"--SMD"`, set by the author
   in an editorial pass over all sixteen letters
   (`docs/design.md#blog-series`, no longer provisional). **Do not change
   it, and do not reapply the old "Dear colleague" / "— Steve" form** —
   that placeholder is gone by decision, and an earlier revision of this
   step told you to restore it from the living doc. The same pass replaced
   em-dashes with colons, parentheses or full stops; that is the series
   register, so anything you write must match it. Do not reintroduce
   em-dashes in `closing.org` or `index.org`.
2. Assign order and numbers: `#+TITLE: Letter <n>: …` in checklist
   order, with [baseline-capture] as Letter 0. Add `#+SERIES_PREV` /
   `#+SERIES_NEXT` slugs.
3. Continuity pass, minimal edits only: a concept explained in full
   twice is explained once and referenced ("as in Letter 3") the second
   time; a term used before it is explained gets a one-clause gloss on
   first use; a "refused" section that names a tactic without saying
   what it does gets the gloss. Do **not** change any claim about what
   was proved or what was found; if two letters contradict each other
   on a finding, the later one wins and the earlier gets a one-line
   bracketed note "[Later: see Letter n]" — that is the epistolary form
   doing its job.
4. Write `blog/letters/closing.org`: "Letter 17: What I'd tell the
   committee" (there are sixteen letters, numbered 0 through 16, so the
   closing letter is 17 — an earlier revision of this step said 14, from
   before three steps were added to the plan). From `docs/design.md#laws-inventory`: the properties
   table in prose, the at-most-one-error condition, the linear-order
   finding, and the one paragraph on whether writing it twice was worth
   it — written for the same reader, not as a paper abstract. Four
   sections as usual; "refused" may be "nothing; this one is a summary".
5. Write `blog/letters/index.org`: series title, one line per letter
   with slug and title, and the reading note "each letter was written
   the day its proof went green".
6. If a `voice` skill or `lexcheck` script is available in the
   environment, run it over every letter with the register it
   documents for blog posts and apply its warnings **mechanically**
   (phrase substitutions), not its judgment calls. If it is not
   available, say so in the handoff to the integration review and
   leave voice for the author.
7. Update `docs/design.md#blog-series` with the final order and the
   index path. The addressee decision is already recorded there and its
   provisional mark is already gone; do not re-add either.
8. Extend `scripts/check-letters.sh` to also require `index.org` to
   list every slug present in `blog/letters/`.

### Verify

`make letters` must pass; `make all` must pass (no code changes
expected — if the letters step needs a code change, that is a block).

### Tests

None.

## Declared file scope

`blog/letters/*.org` (edits), `blog/letters/closing.org`,
`blog/letters/index.org`, `scripts/check-letters.sh`, `docs/design.md`
(`#blog-series`). No file under `Graded/`, `Tests/`, `Examples/`.

## Spot checks

```
grep -l "SERIES_NEXT" blog/letters/*.org | wc -l
grep -c "^- " blog/letters/index.org        # letters + closing
git diff --stat integration/lean-model -- Graded Tests Examples   # empty
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-blog-series-edit -b step/blog-series-edit integration/lean-model
cd ../wt-blog-series-edit
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-blog-series-edit.md`
(the integration branch is broken; not your step to fix).

## Verify GREEN after

```
V0=$(date +%s); make verify > /dev/null; echo verify=$?; V1=$(date +%s)
make nosorry; echo nosorry=$?
make letters; echo letters=$?
```
All zero. Read `tail -n 20 build.log` only; never the whole log.

## Commit and merge back

```
git add -A
git commit -F- << 'MSG'
blog-series-edit: order, index and continuity pass over the letters; closing letter

Turns sixteen per-step letters into a series for a Lean-naive
reader without altering any finding. This is the one step allowed to
read every letter, once. Contradictions between letters are annotated,
not resolved, because the letters are the record of what was learned
in what order.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/blog-series-edit -m "merge step/blog-series-edit [blog-series-edit]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-blog-series-edit
printf '%s\n' '{"step":"blog-series-edit","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/blog-series-edit | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-blog-series-edit
git branch -d step/blog-series-edit
```

## Handoff

Mark `blog-series-edit` done in `tmp/plan/checklist.md`. There is no next step file. Write
`tmp/plan/handoff-integration-review.md` fresh, per the contract in
`AGENT-PROMPT.md`, addressed to the Opus integration consult: what the
voice tool did or didn't do, any letter contradiction you annotated, and
anything in `docs/design.md` that is still marked provisional.
