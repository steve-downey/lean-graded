# handoff → graded-carrier

Goal and merge criterion: fixed by `step-graded-carrier.md`.

## Give every new file a module doc-string

Mathlib's style linter (`linter.style.header`) fires a warning whenever a
file's *module*-level doc-string (`/-!  ... -/`, distinct from a `/-- ... -/`
attached to one declaration) isn't the first command right after the
imports. Give **every** new `.lean` file (`Graded/Carrier.lean`,
`Examples/Validation.lean`, `Tests/Carrier.lean`) one, as the very next
command after its imports and before `namespace ...` — mirror
`Graded/Prelude.lean`'s shape. I had to add them to `Graded/Grade.lean` and
`Tests/Grade.lean`.

(Historical note, in case you see it referenced elsewhere: this warning used
to *fail* `make verify`, because the recipe also grepped build.log for the
string "error" and the linter's warning text quotes back the code it is
complaining about — docstrings in this project say "error" constantly. The
orchestrator removed that grep after my step; `lake`'s exit status is now
the signal. So a missing module doc-string is a warning you should fix, not
a build failure. The Makefile is out of scope for you; don't touch it.)

## A step-file identifier is stale for this Mathlib pin: `Finset.not_mem_empty`

Your step file says to eliminate the `err` case of `emptyEquiv` via
`Finset.not_mem_empty`. At the pinned Mathlib commit
(`85e3a25e006c35636f0e53b0e9296caca2685bc0`, `docs/design.md#toolchain`),
that lemma is named **`Finset.notMem_empty`** (camelCase "Mem"), defined in
`Mathlib.Data.Finset.Empty` (reached via `Mathlib.Data.Finset.Defs`). I
confirmed this by grep, not by building your file — I did not touch
`Graded/Carrier.lean`. If it isn't already visible through your imports,
follow the same pattern I used for `Finset.empty_union`/`union_empty`
(needed `Mathlib.Data.Finset.Lattice.Lemmas`, one level past
`Finset.Basic`): widen the import on the specific file that needs it, not
`Graded/Prelude.lean`.

## `docs/design.md#grade` is filled

`Graded.Grade`, `Grade.bot`, `Grade.join` and all thirteen named lemmas
(`join_assoc`, `join_comm`, `join_idem`, `bot_join`, `join_bot`,
`le_join_left`, `le_join_right`, `join_le`, `join_mono`, `le_refl'`,
`le_trans'`, `bot_le`, `join_eq_right_of_le`) exist in `Graded/Grade.lean`
and are documented at `docs/design.md#grade`, including which five carry a
`PROPERTY:` tag. `Grade` is *not* a Mathlib instance (by design — see that
section). Nothing else changed outside `Graded.lean`, `Graded/Grade.lean`,
`Tests.lean`, `Tests/Grade.lean`, `docs/design.md` (`#grade` only), and
`blog/letters/grade-pomonoid.org`.

## Merge commit

`step/grade-pomonoid` merged into `integration/lean-model` at `bb27127`
(`--no-ff`). `integration/lean-model` is GREEN (`make verify`, `make
nosorry`, `make letters` all exit 0) as of that commit.
