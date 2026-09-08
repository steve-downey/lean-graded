# handoff → oracle-export

Goal and merge criterion: fixed by `step-oracle-export.md`.

## What changed underneath you

[grade-obligations] merged. It added `Graded/Obligations.lean` (new),
`Tests/Obligations.lean` (new), `blog/letters/grade-obligations.org`
(new), `docs/design.md`'s new `## obligations` anchor (between
`#ungraded-baseline` and `#laws-inventory`), and one import line each in
`Graded.lean`/`Tests.lean`. **No existing `Graded/*.lean` module changed**
(spot-checked) — every theorem and every `PROPERTY:` tag your script
already expects in `Graded/Grade.lean`/`Graded/Morphism.lean` is exactly
where and what it was.

## `Graded/Obligations.lean` is inside your `Graded/*.lean` glob

Your script parses every `theorem <name>` in `Graded/*.lean`, so it will
also see this file's five new theorems: `foldG_le`, `foldG_cons_ne_nil`,
`joinAllG_perm`, `join_le`, `nat_not_idem`. These are generic — stated
over an abstract `[Pomonoid G]`/`[IsCommPomonoid G]`/`[IsIdemPomonoid G]`,
never over `Graded.Grade` or `Graded g α` — so treat them as a *second*,
separate set of rows, not a correction to the existing per-`Grade` ones.

**Name collision to watch for, not a bug in either file.** This step adds
a *new* theorem named `join_le` (`Graded.join_le`, generic, in
`Graded/Obligations.lean`) alongside the *existing* `Graded.Grade.join_le`
(`Graded/Grade.lean`, unchanged). Same bare name, different namespace,
different hypotheses, different proof — your heuristic's mention-scan is
namespace-blind, so don't merge them into one table row. Likewise
`Graded.foldG_le` (this step, generic) is a different theorem from
`Graded.Traverse.foldGrade_le` (existing, concrete) — again, same shape
of name, deliberately, and deliberately two different things.

**The one finding that matters for your verdict paragraphs.** Your step's
own §3 bullet list says "which needed only the order (`widen_*`,
`foldGrade_le`, the public `traverse` definition)" — that bullet is still
correct as stated, for the *existing*, concrete `foldGrade_le`
(`Graded.Traverse`, cites `Grade.join_le`/`Grade.bot_le`, no idempotence,
unchanged by this step). But the *generic* sibling `foldG_le`
(`Graded.Obligations`) needs `IsIdemPomonoid`, not `Pomonoid` alone,
because this step deliberately did **not** give the generic `Pomonoid`
class a primitive `join_le` field (a `Nat` instance under `+` can't
satisfy one — see `docs/design.md#obligations`, "What was deliberately
not copied"). If your bullet list is meant to describe the *generic*
obligation layer rather than just the existing per-`Grade` proofs, word
it as: bounded (`foldG_le`) and exact (`foldG_cons_ne_nil`) both cost
idempotence generically; only order-independence (`joinAllG_perm`) is
free of it. Don't state both framings as if they agree — they answer
different questions (what a *concrete* `Grade` proof happens to cite,
versus what the *abstract* obligation requires) and the whole point of
[grade-obligations] was that those two answers differ for exactly this
theorem.

## Vocabulary you'll want for "what a different grade pomonoid must supply"

Your own §3 asks for a verdict bullet on this. `docs/design.md#obligations`
already has it, worked out and named:

- `Pomonoid`: `join`, `bot`, `le`, `join_assoc`, `bot_join`, `join_bot`,
  `le_refl'`, `le_trans'`, `bot_le`, `join_mono`.
- `IsCommPomonoid extends Pomonoid`: `join_comm`.
- `IsIdemPomonoid extends IsCommPomonoid`: `join_idem`.
- Layer-to-law: `foldG_le → IsIdemPomonoid`; `foldG_cons_ne_nil →
  IsIdemPomonoid`; `joinAllG_perm → IsCommPomonoid`.

Cite the anchor rather than re-deriving the table; it also has the
Mathlib classes considered (`SemilatticeSup`, `IsOrderedAddMonoid`,
`CovariantClass`) and why none were inherited from, and the `Nat`
counter-instance's two disproofs, if useful color for your own report.

## Everything else

Your step's own "What already exists" and "The change" sections are
otherwise unaffected. `docs/laws.md`/`docs/laws.json`/`docs/probe-harness.md`
are new files under your own declared scope; nothing here constrains
their shape beyond the note above.
