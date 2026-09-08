# handoff → blog-series-edit

Goal and merge criterion: fixed by `step-blog-series-edit.md`.

## Letter count: sixteen, not thirteen

Your own step file's "Why" section says "thirteen honest letters" and
step 4 numbers the closing letter "Letter 14". Both predate
[ungraded-baseline], [grade-obligations], and [oracle-export], which each
added one more. `blog/letters/*.org` currently holds sixteen: one per
checklist step 1–16, no gaps, no extras (confirmed by `ls`). With
[baseline-capture] as Letter 0 per your own renumbering rule, the other
fifteen are Letters 1–15 in checklist order, and `closing.org` — being
written after all of them — is Letter 16, not Letter 14. Don't take "What
I'd tell the committee" as pinned to a specific number; recompute it from
the actual count.

`blog/letters/oracle-export.org` currently self-numbers as "Letter 16"
(following the naive pattern of citing its own checklist step number,
which [grade-obligations].org also does at "Letter 15") — this is exactly
the kind of number your continuity pass fixes; expect to renumber all
sixteen, not just the newest one.

## What `oracle-export` adds for your closing letter

Your step 4 says the closing letter should draw its properties-table
prose, at-most-one-error condition, and "the linear-order finding" from
`docs/design.md#laws-inventory`. That section now exists, freshly written
this step, with the corrected counts — use it directly rather than
re-deriving from the letters:

- The properties table is [`docs/laws.md`](../../docs/laws.md) (146
  theorems, generated, cited from `#laws-inventory`).
- Commutativity: **six** sites (`ap_flip`, `flatten_comm`,
  `Comp.grade_reassoc`, `Graded.Tuple.joinAll_perm` **and**
  `join_mem_eq`, plus a seventh generic confirmation), not the three
  several earlier letters may say — if any implementation letter states
  "three places," that is superseded by `#laws-inventory` and should get
  your "[Later: see Letter 16]"-style bracketed note per your own rule 3,
  not a silent rewrite.
- The at-most-one-error condition: **four** sites, and they are four
  *different* answers (load-bearing in `ap_flip`; stated but not needed
  in `Accum.toGraded_grade`; not needed at all in `flatten_comm`; a
  different three-way condition in `flatten_ap`) — not the same finding
  four times. This is probably the single most important correction for
  the closing letter to get right; my own letter's "Back in C++" section
  only gestures at it, `#laws-inventory` has the full account.
- The linear-order finding is [canonical-representation]'s
  (`docs/design.md#representation`, `Canon` needing `[LinearOrder Err]`
  where `Grade` needs only `[DecidableEq Err]`) — `#laws-inventory` does
  not restate it; go to that anchor directly.

## Still provisional, untouched by this step

`docs/design.md#blog-series`'s addressee ("Dear colleague") is exactly as
it was — I read it, wrote to it, changed nothing there, per my declared
scope. [grade-join-strength](../../docs/design.md#grade-join-strength) is
still OPEN: `#laws-inventory`'s closing paragraph notes that it governs
how the table's "idempotent" column should be read (under the stronger
reading, `join_idem` is a theorem, not an axiom) without answering it.
Neither is yours to resolve; both are candidates for "still marked
provisional" in your own handoff to the integration review.

## Everything else

`scripts/check-letters.sh` currently checks four headings per letter and
nothing about `index.org`; your step 8 extends it. No `Graded/`, `Tests/`,
or `Examples/` file changed this step (only `Makefile`,
`docs/design.md`'s `#laws-inventory`, `docs/laws.md`/`docs/laws.json`/
`docs/probe-harness.md`, `scripts/laws-inventory.py`,
`blog/letters/oracle-export.org`) — your own spot check
(`git diff --stat integration/lean-model -- Graded Tests Examples`) will
still come back empty after this merge, same as before it.
