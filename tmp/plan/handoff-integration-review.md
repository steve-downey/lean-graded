# handoff → integration-review

Goal and merge criterion: fixed by `INTEGRATION-REVIEW.md`.

## Numbering deviation: closing letter is 16, not the literally-stated 17

The step file (and its own commit message, `a4eadf6`) says "sixteen
letters, numbered 0 through 16... the closing letter is 17." That is not
achievable: sixteen 0-indexed items span 0-15, not 0-16 (17 is 17 slots).
Ground truth confirmed 16 letter files exist, one per checklist step 1-16.

Before this step, `baseline-capture` through `subsumption-widen`
(checklist steps 1-4) already self-numbered correctly as Letters 0-3. But
`monad-laws` (step 5) through `oracle-export` (step 16) all self-numbered
one too high (5-16 instead of 4-15) — matching their raw checklist step
number rather than continuing the "step number minus one" pattern the
first four letters already used. That is a real, systematic off-by-one
bug, not a deliberate gap.

I fixed it: renumbered `monad-laws` through `oracle-export` down by one,
giving a clean, gap-free 0-15 across all sixteen existing letters, and
set `closing.org` to **Letter 16** (not 17). This is the only numbering
consistent with "baseline-capture is Letter 0" and the actual count of
sixteen files. If the author actually wants a gap at some number so the
closing letter lands on 17, that is a real editorial call this step did
not have standing to make unilaterally — flagging it here rather than
guessing further. `docs/design.md#blog-series` records the numbering
scheme and the reason for the correction.

## Voice tooling: deliberately skipped on the sixteen existing letters

No `voice` skill or `lexcheck` script was run over the sixteen pre-existing
letters, on purpose: the step file's own amendment says the author had
just hand-edited all sixteen (addressee, signature, em-dashes) and a tool
pass would fight that. I did not invoke any tool on them; I only made
manual, targeted continuity edits. I did read `closing.org` and
`index.org` (the two files I authored) back myself for the same register
(no em-dashes, "Steve,"/"--SMD") but ran no automated tool on them either
— none was invoked this session at all.

## What I found and fixed beyond the step file's own description

The step file's `docs/design.md#blog-series` anchor said the author's
editorial pass (commit `e1fa465`) covered "all sixteen letters." It
actually touched only ten (`git show --stat e1fa465`): the addressee/
signature/em-dash pass never reached `graded-morphism.org` (already had
"Steve,"/"--SMD" from creation but kept em-dashes), `canonical-
representation.org`, `compose-applicative.org`, `ungraded-baseline.org`,
`grade-obligations.org`, and `oracle-export.org` (all five still had
"Dear colleague," / no "--SMD" signature / em-dashes throughout). I
brought all six into the same register as the other ten, since the step
brief is explicit that "Dear colleague" and em-dashes must not survive
anywhere in the series and that register is now decided project-wide.
This is squarely inside "continuity pass, minimal edits" — punctuation
and salutation only, no claim changed.

## Contradictions annotated: none needed

I checked for the "three places" vs. "four/six" corrections the prior
handoff flagged as likely needing a bracketed `[Later: see Letter n]`
note. I found no letter other than `oracle-export.org` itself claiming a
specific count for commutativity or the at-most-one-error condition;
`oracle-export`'s self-correction ("I'd said... it's actually...") refers
to its own earlier narration/the plan's predictions, not to another
letter, and it already reads honestly in place. I found no genuine
letter-vs-letter contradiction requiring annotation. The two real
reversals in the project (the flattened composition law refuted then
replaced by the unflattened one in `compose-applicative.org`; the
at-most-one-error hypothesis needed in only one of four sites) are already
narrated honestly within the letters that make them and did not need a
bracketed note.

I did trim two duplicate full explanations (continuity pass item 3):
`monad-laws.org`'s repeat of `subst e` now points back to Letter 3; and
`compose-flatten.org`'s repeat of the universe-mismatch explanation now
points back to Letter 8's `GList`.

## Still provisional / open in `docs/design.md`

- [`grade-join-strength`](../../docs/design.md#grade-join-strength) — OPEN.
  Whether a grade's join must be a least upper bound; under the stronger
  reading `join_idem` becomes a theorem rather than an axiom. `closing.org`
  states this as the series' one open question, honestly, without
  resolving it.
- [`graded-traversable-composition`](../../docs/design.md#graded-traversable-composition)
  — marked CLOSED by [compose-applicative], but `docs/design.md`'s own
  `provisional-decisions` index still lists it under "OPEN question" text
  saying "whether a Compose-aware version is worth building is undecided."
  That undecided sub-question is real and still open even though the
  refutation itself is closed; not mine to resolve.
- The `#blog-series` anchor's addressee paragraph still says the author's
  pass covered "all sixteen letters" when the commit touched ten; I did
  not correct that sentence (out of my declared file scope beyond
  ordering/index), only the *effect* is now true across all sixteen files.

## Everything else

`Graded/`, `Tests/`, `Examples/` are untouched (confirmed by
`git diff --stat integration/lean-model~1...step/blog-series-edit --
Graded Tests Examples`, empty). Merge commit: `c18b248`. Files touched:
`blog/letters/*.org` (all sixteen, continuity edits), `blog/letters/
closing.org` and `index.org` (new), `scripts/check-letters.sh` (extended
to require `index.org` list every slug in `blog/letters/`), `docs/
design.md` (`#blog-series` only).
