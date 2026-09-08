# handoff → cast-burden-migration-scope (open question, not a step)

[sufficient-grade-applicative] is done and merged
(`18a4111213cd5345596fb076ad980525437f4ac0` into `integration/lean-model`).
This is not a step handoff; it is the evidence
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope)
asks for, addressed to whoever writes that open question's brief next.

## The headline number

`Comp.ap_interchange` (the two-coordinate composite's interchange law,
`Graded/ComposeApp.lean`): **six** `cast`-substring occurrences across
its statement+proof, driven by two `Comp.castGH` calls (each bundling
two `Graded.cast`s). Its sufficient-grade analogue, `Comp.apK_interchange`
(`Graded/Sufficient.lean`): **zero**, statement and proof combined, and
the proof is a plain 3-way `cases` down to `rfl` — no property cited at
all, where the union-graded version cites `Graded.ap_interchange`
(unit, twice) explicitly.

The single-layer four applicative laws also went to zero casts each
(`ap_pure_id`/`ap_pure_pure`/`ap_interchange`/`ap_comp` each carried 1-2;
their `apK_*` analogues carry 0), and every one of the four now cites
only `Grade.le_refl'` in its statement, never a unit or associativity
lemma — the same "order replaces unit/associative" shift
[sufficient-grade-bind] found for `bind`'s three laws.

## The threaded-obligation question: resolved more sharply than predicted

The step brief predicted `apK` would need three threaded hypotheses
where `bindK` needs two, free at worst by proof irrelevance the way
`bindK_irrel` makes `bindK`'s two free. It came out better than that:
`apK` takes exactly the same **two** hypotheses `bindK` does
(`hg : g ⊆ k`, `hh : h ⊆ k`). The predicted third one (for `pure`'s own
grade) never appears in the signature at all, because `pureK` (already
established: `pure` widened to any grade directly, not pinned to
`Grade.bot`) needs no inclusion proof of its own to land at `k`. Not
"free by irrelevance" — simply absent. `Comp.apK` correspondingly needs
four (two per coordinate, matching the step's "two coordinates each
needing their own" prediction), not six.

## The commutativity finding — the one that matters most

`apK_flip` (`apK hg hh f x = apFlippedK hg hh f x`, under the same
one-sided "at most one side is `ok`" condition `ap_flip` needs) proves
with **no `Grade.join_comm` anywhere**, because at a common sufficient
grade `k` there is no second expression for the grade to compare against
the first — `ap_flip` needs `join_comm` *by construction*, comparing
`Grade.join g h` against `Grade.join h g`; `apK`/`apFlippedK` both
already land in the same `Graded k β`. `Comp.apK_interchange` confirms it
at the composite scale (also zero casts, also `join_comm`-free, also no
property cited).

**This revises [grade-obligations](../../docs/design.md#obligations)**,
which currently attributes commutativity's necessity to the
applicative's order-independence (combining the same two values in
either order needs matching grades). The sharper reading: the
applicative itself never needs `join_comm`, at any sufficient grade,
including the exact union. Commutativity is the price of *computing the
grade as a canonical, exact union* and then insisting the two
computation orders be recognized as the same type — a cost of
canonicalization, not a requirement the applicative interface imposes.
`docs/design.md#applicative`'s new subsection states this in full; the
letter (`blog/letters/sufficient-grade-applicative.org`, Letter 18)
carries the same finding to the C++ reader: `error_set`'s union needs
`join_comm` because P3200 canonicalizes it into one type per set of error
kinds regardless of call-site order, not because applying a graded
function to a graded argument inherently needs it.

## What I did not touch, and where I'd start

This step's declared scope was `ap`/`map2`/`Comp.ap` only. Two cast sites
this step's own docs cross-reference are still exactly as they were:

- `Comp.traverseComp_cons` (`Graded/ComposeApp.lean`) still casts along
  `Grade.join_idem`, once per component — the same shape `traverse_cons`
  (`Graded/Traverse.lean`, single-layer) casts along, for the same
  reason (folding a uniform grade over a list is idempotent, not unit).
- `GradedHom`'s cast-quantified *fields* (`Graded/Morphism.lean`,
  referenced at `docs/design.md#monad`'s verdict paragraph) — casts
  inside a record's field types, not a theorem's statement.

**My recommendation: `traverse` next, then `flatten`, then `Comp`
(what's left of it), then `GradedHom` last.**

- `traverse` first: it is the *same* technique (a caller-supplied
  sufficient grade instead of a folded one) applied to a mechanically
  similar situation (idempotence collapsing a fold, the way unit/
  associativity collapsed `bind`/`ap`'s joins), on the module this step
  already touched half of (`Comp.traverseComp_cons` lives beside
  `Comp.apK` in the same file). Continuing here is the least speculative
  next step: the pattern is proven twice already (monad, applicative),
  and `foldGrade_le`'s cast-free "widen once" shape (already used by
  `traverse`/`traverseComp` today) suggests the sufficient-grade version
  may not even need a new fold, just a `k`-indexed reduction lemma set
  the same shape `apK`'s were.
- `flatten` second: `flatten_ap`'s conditional counterexample is an
  *explanation* of where the union-graded design breaks, not a law with
  a cast burden to remove the same way — lower mechanical payoff, but
  natural to revisit once `traverse`'s sufficient-grade layer exists,
  since `flatten` sits between the two.
- `Comp` third, to close out what `traverseComp_cons` leaves: by then
  the composite's own idioms (`Comp.widenGH`/`Comp.castGH` mirrors) will
  already have a `traverse`-side sufficient-grade analogue to reuse.
- `GradedHom` last, and flagged as likely **not** a "beside it" extension
  at all: cast-quantified *fields* mean the record's own type carries the
  cast, not a theorem about it — fixing that plausibly means changing
  `GradedHom`'s definition itself, which is exactly the shape
  `AGENT-PROMPT.md` says to halt on (`amendment-*`, not silently
  reshape). Whoever picks this up should expect to write an amendment
  before writing a proof.

## Files touched this step

`Graded/Sufficient.lean` (extended, not forked — `Graded/Applicative.lean`
and `Graded/ComposeApp.lean` untouched), `Tests/Sufficient.lean`,
`Examples/Validation.lean` (`sumTwoK`), `docs/design.md`
(`#applicative` new subsection, `#monad`'s table extended),
`scripts/laws-inventory.py` (10 ALLOWLIST entries, each justified
individually — the pure `ok`/`err` reduction lemmas for `apK`/
`apFlippedK`/`Comp.apK`, plus `apK_flip` itself, which is structural by
the same "nothing to compare" argument as the commutativity finding
above), `blog/letters/sufficient-grade-applicative.org` (Letter 18),
`blog/letters/index.org`.
