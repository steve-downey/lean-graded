# handoff → sufficient-grade-applicative

**Verdict from [sufficient-grade-bind]: YES, proceed.** The cast-free
layer measured strictly cheaper for `bind`: 0 casts in all three law
statements (down from 1 each), shorter proofs (13/1/3 lines against
21/3/9), and the two threaded `⊆` proofs a call site pays are free by
`bindK_irrel`, which is `rfl`. Run this step.

## What is already on disk, exactly as your step file expects

`Graded/Sufficient.lean` exists with `bindK`, `pureK` (`:= fromEmpty`),
reduction lemmas `bindK_ok`/`bindK_err`/`widen_ok`/`widen_err`, the three
cast-free laws `bindK_pure_left`/`bindK_pure_right`/`bindK_assoc`,
`bindK_widen`, `bindK_irrel`, and the bridge `bind_eq_bindK` (tagged
`/-- BRIDGE -/`). Extend this file; do not create a second one.
`Tests/Sufficient.lean` and `Examples/Validation.lean` (`validateK`) are
also in place, both registered in `Tests.lean`/nothing new needed in
`Graded.lean` beyond the existing `import Graded.Sufficient`.

## The one thing your step file cannot tell you and needs from me

**`bindK_irrel` is free by literal `rfl`, no case split, no
`Subsingleton.elim` invocation needed.** That is the fact your step's own
"three subsumption obligations instead of two" cost analysis depends on:
if `apK`'s extra threaded proof is *also* free the same way (and there is
no reason it would not be: it is the same `Finset`-is-a-`Prop` argument,
not something specific to `bindK`'s two-argument shape), the obligation
count going from two to three should not change the verdict, only the
statement's parameter list.

## The property-shift pattern, confirmed mechanically

Every cast-free law cites an **order** lemma (`Grade.bot_le`,
`Grade.le_refl'`) where its union-graded counterpart cited a **unit** or
**associativity** lemma. This is not asserted, it came out of
`scripts/laws-inventory.py`'s own mention scan after I added the ALLOWLIST
entries. Expect `apK_interchange`/`apK_comp` to show the same pattern:
`join_mono`/`le_refl'`/`le_trans'` in, `join_assoc`/`bot_join`/`join_bot`
out. If a law shows up citing something else entirely, that is worth a
second look before you write the letter.

## `scripts/laws-inventory.py`: a chunking trap I hit, so you do not have to

The script's chunker attributes a **trailing** `--` comment (not a `/--`
docstring) to the **preceding** theorem, not the one it is actually
describing, unless a `-- ---...` (3+ dash) separator line sits between
them. I had `bindK_irrel` silently and wrongly credited with "order"
because the next theorem's explanatory comment mentioned
`Grade.le_join_left`/`Grade.le_join_right` and bled into `bindK_irrel`'s
chunk. Put a `-- ---------------------------------------------------------------------`
separator line before any explanatory comment block that precedes a new
theorem, the way the rest of the file (and `Examples/Validation.lean`)
already does, or the inventory will misattribute properties silently
(no build failure, just a wrong row in `docs/laws.md`).

Also: any theorem that is a pure `ok`/`err` reduction (mirroring
`bindK_ok`/`bindK_err`/`widen_ok`/`widen_err`) will need an ALLOWLIST
entry, same as those four did. `apK`'s reduction lemmas almost certainly
will too. Justify each individually; do not batch them under one reason.

## The landmine your step file already named, restated with the evidence I have

`bind`'s cast-free layer never had to compare two different joins against
each other, because `bindK` never computes a join at all: everything
lands in the same caller-supplied `k`. `ap_flip` is the first place in
this whole model that compares `join g h` against `join h g` directly. I
did not build an `ap_flip` analogue (out of my scope), so I cannot tell
you whether it needs `Grade.join_comm` or not. Genuinely open, exactly as
your step file says.

## Style notes carried forward

Letter 17 (`blog/letters/sufficient-grade-bind.org`) has no em-dashes
throughout, per the letter template's discipline. Grep your own letter
for `—` before you finish; it is easy to reach for one describing a
before/after contrast, which is most of what this step is about.
`blog/letters/index.org`'s intro paragraph now says "Eighteen letters"
and explains the series continued past Letter 16; update the count
again when you add Letter 18, and add your entry after Letter 17's line.
