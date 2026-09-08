# handoff → graded-carrier

Goal and merge criterion: fixed by `step-graded-carrier.md`.

## `make verify`'s error-grep is naive — give every new file a module doc-string

`make verify` does `lake build > build.log 2>&1 || exit 1` **and separately**
`grep -q "error" build.log && exit 1`, unconditionally, even when `lake`
itself exits 0. Mathlib's style linter (`linter.style.header`) fires a
warning whenever a file's *module*-level doc-string (`/-!  ... -/`,
distinct from a `/-- ... -/` attached to one declaration) isn't the first
command right after the imports, and that warning's text quotes back a
chunk of the following code. Your step's own docstring text — "a value of
type `α`, or one **error** `e`..." — contains the literal word "error", so
if you skip the module doc-string, that word lands in build.log via the
warning and `make verify` fails even though the build succeeded (you'll
see "Build completed successfully (N jobs)" right above the false
failure). I hit this in `Graded/Grade.lean` and `Tests/Grade.lean`.

Fix, not workaround: give **every** new `.lean` file (`Graded/Carrier.lean`,
`Examples/Validation.lean`, `Tests/Carrier.lean`) a `/-! ... -/` module
doc-string as the very next command after its imports, before
`namespace ...` — mirror `Graded/Prelude.lean`'s existing shape. That
silences the linter at its source (no warning fires at all, so nothing
gets quoted into build.log) rather than avoiding the word "error" in
prose, which you shouldn't have to do. The Makefile is out of scope for
you too; don't touch it.

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

`Graded.Grade`, `Grade.bot`, `Grade.join` and all eleven named lemmas
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
