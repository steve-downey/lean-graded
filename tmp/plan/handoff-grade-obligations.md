# handoff → grade-obligations

Goal and merge criterion: fixed by `step-grade-obligations.md`.

## What changed underneath you

[ungraded-baseline] merged first. It touched only `Graded/Ungraded.lean`
(new), `Tests/Ungraded.lean` (new), `blog/letters/ungraded-baseline.org`
(new), `docs/design.md` (new `## ungraded-baseline` anchor), and one
import line each in `Graded.lean`/`Tests.lean`. **`Graded/Grade.lean` is
untouched** — every lemma name your step cites (`join_assoc`, `bot_join`,
`join_bot`, `le_join_left`, `le_join_right`, `join_le`, `join_mono`,
`le_refl'`, `le_trans'`, `bot_le`, `join_comm`, `join_idem`) is exactly
where and what it was.

`docs/design.md` now has 15 top-level anchors: `#toolchain`,
`#cpp-counterpart`, `#grade`, `#carrier`, `#subsumption`, `#monad`,
`#applicative`, `#traverse`, `#compose`, `#morphisms`, `#representation`,
`#ungraded-baseline`, `#laws-inventory`, `#blog-series`,
`#provisional-decisions`. Your step's own instruction —
new anchor `## obligations` immediately after `## ungraded-baseline` —
lands it right before `## laws-inventory`, exactly as before this anchor
existed; nothing about your insertion point changes.

`Graded.lean` and `Tests.lean` each gained one import line
(`Graded.Ungraded`, `Tests.Ungraded`) at the end of their lists. You will
append your own (`Graded.Obligations`, `Tests.Obligations`) after those —
an ordinary append, no conflict.

## A data point for your layering table, not a dependency

Not required reading, but since your step's whole point is which
pomonoid layer buys which law: [ungraded-baseline] found that fixing
*every* grade in `bind`/`ap`'s general laws to one single value makes
`Grade.join_assoc` and `Grade.bot_join`/`Grade.join_bot` disappear from
the proofs entirely (`bindF_assoc`, `apF_comp` in `Graded/Ungraded.lean`)
— only `Grade.join_idem` survives, cited through two small reduction
lemmas (`bindF_ok`/`bindF_err`). That's the mirror image of your own
demonstration: yours varies the *grade* (a non-idempotent `Nat` pomonoid)
and shows a law stops typechecking; that one varies *how many distinct
grades appear* (one, instead of several) and shows two properties stop
being *needed* even though the grade itself stays a perfectly good
idempotent pomonoid throughout. Both are evidence for the same "layered,
not monolithic" claim; cite `[ungraded-baseline]`'s `#ungraded-baseline`
anchor if it's useful color for your own table, but nothing in your
step's own content depends on it.

## Everything else

Your step's own "What already exists" (`#grade`, `#traverse`) and "The
change" sections are self-contained and unaffected by
[ungraded-baseline]'s merge. No correction to your step file is needed.
