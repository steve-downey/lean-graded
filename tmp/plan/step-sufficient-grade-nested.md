# step: sufficient-grade-nested

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

Last of three legs. **This step closes
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope).**
Planned 2026-09-08.

## Why

The two nested-carrier structures are what remains: `Graded/Compose.lean`
(`flatten`, `swap`, 8 theorems, 4 with a cast in their statement, including
`flatten_comm` which is 16 lines of pure bookkeeping) and
`Graded/ComposeApp.lean` (`Comp`, `traverseComp`, 13 theorems, 6 with a
cast). They are one step because the work is the same shape on the same
subject, and because the earlier legs have made the technique routine:
reduction lemmas first, then laws that state at a common `k`.

Two specific things here are worth more than the cast counts.

**`flatten` is the operation whose whole job is to change a grade.** Every
other operation was migrated by letting the caller nominate the result
grade, which removed the grade arithmetic. `flatten`'s *purpose* is to
collapse `Graded g (Graded h α)` into one grade, so a sufficient-grade
`flattenK (hg : g ⊆ k) (hh : h ⊆ k) : Graded g (Graded h α) → Graded k α`
does not remove the operation, it removes the obligation to name the union
specifically. Whether `flatten_comm` then has an analogue at all is the
question: it exists to say the two layers can be swapped, and at a common
`k` there may be nothing left to say. **If it disappears rather than
becoming cast-free, say so** — that is a different result from the earlier
legs and it belongs in the letter.

**`Comp.grade_reassoc` is the last commutativity citation standing.**
[obligation-layering] classified it as canonicalization: a pure
grade-level equation reassociating `(g ⊔ h) ⊔ (g' ⊔ h')` into
`(g ⊔ g') ⊔ (h ⊔ h')`. At two common grades `k₁`, `k₂` both sides are
already `(k₁ ⊔ k₂)`-shaped and the equation should be `rfl` or absent. If
so, the model's commutativity citations drop to `Grade.join_comm` itself
plus the canonicalization facts in `Tuple.lean` — and the claim "no
operational law in the model needs commutativity" becomes visible in the
code rather than argued in a table.

## What already exists

`docs/design.md#compose` (`flatten`, `swap`, the eight laws,
`flatten_comm` unconditional, `Comp`, `Comp.ap`, `traverseComp`,
`traverseComp_eq`, `flatten_ap` and its disjunctive hypothesis,
`Comp.grade_reassoc`), the three sufficient-grade subsections at `#monad`,
`#applicative` and `#traverse`, `#morphisms`' (added by the previous leg),
and `#obligations`' classification table. `Graded/Sufficient.lean` holds
everything the earlier legs built, with its `/-- BRIDGE -/` theorems.

## The change

Extend `Graded/Sufficient.lean`.

- `flattenK` as above, reduction lemmas first, then analogues of
  `flatten_map`, `flatten_pure_outer`, `flatten_pure_inner`,
  `flatten_flatten`, and the two `flatten_widen_*`. Report each one's cast
  count against its original and the property it consumed.
- `flatten_comm`'s analogue **or a recorded reason there is none.**
- `flatten_eq_flattenK`, the bridge, tagged `/-- BRIDGE -/`.
- `CompK` at two sufficient grades, `CompK.apK`, and the analogue of
  `Comp.grade_reassoc` — or the finding that it is unnecessary.
- `traverseCompK` and `traverseComp_eq`'s analogue. Note that
  `traverseComp_eq` is the theorem that *holds* unconditionally and closed
  the composition question; its analogue existing cast-free is a
  confirmation, and its analogue failing would be a serious finding about
  the sufficient-grade design, not a minor one.
- `flatten_ap`'s analogue. The union version needs a three-way disjunctive
  hypothesis discovered during its proof, and `Comp.grade_reassoc`'s
  `join_assoc` + `join_comm`. **Expect the grade half to dissolve and the
  value half to survive**: the hypothesis is about which error a caller
  sees, which no amount of grade nomination changes. If the hypothesis
  *does* dissolve, check very carefully that the statement still says
  something — a law that became unconditional because it became vacuous is
  the one failure mode this leg could hide.

### Closing the question

Update
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope)
in place: move what the three legs settled into a settled section, set
`Status:` to CLOSED if they settled it, and if any part remains open say
exactly which and what would settle it. Do not open a second question on
the same subject. Then write the summary the question was really for: a
single table of every structure in the model, its cast-in-statement count
before and after, and one line on whether the sufficient-grade version is
a strict improvement or a trade.

Also revisit
[grade-join-strength](../../docs/design.md#grade-join-strength): it was
narrowed to "only `traverse` is at stake". The traversal leg will have
either produced a grade that is a `Pomonoid` but not an
`IsCanonicalPomonoid` and still wants `traverse` — the concrete case that
settles it — or not. Record which, and close it if the case exists.

### Consumer

`Examples/Validation.lean`: the `lookup`/`flatten` consumer rerun through
`flattenK`, `#guard`ed identical. Leave the existing one alone.

### Tests

Extend `Tests/Sufficient.lean`, including one two-coordinate instance where
both `k`s are strictly larger than their joins.

### Living doc

`docs/design.md#compose`: a `### The sufficient-grade layer` subsection
covering both structures.

### Letter

`blog/letters/sufficient-grade-nested.org`, **Letter 22**, and it is the
last of the migration. Two subjects a C++ reader can use: `flatten` is the
one operation whose job *is* grade arithmetic, so it shows what the
sufficient-grade discipline does and does not remove; and if
`Comp.grade_reassoc` evaporates, the model then contains no operational
commutativity citation at all, which is the sentence P3200's companion
paper wants. Series register: addressee `"Steve,"`, signature `"--SMD"`,
**no em-dashes**. Add it to `blog/letters/index.org` after Letter 21.

## Declared file scope

`Graded/Sufficient.lean`, `Tests/Sufficient.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#compose`,
`#cast-burden-migration-scope`, `#grade-join-strength`),
`blog/letters/sufficient-grade-nested.org`, `blog/letters/index.org`,
`scripts/laws-inventory.py` (`ALLOWLIST` only), `docs/laws.md` and
`docs/laws.json` (regenerated).

**Neither `Graded/Compose.lean` nor `Graded/ComposeApp.lean` may be
edited**, nor any other operational module. If you must, that is
`amendment-sufficient-grade-nested.md` and a halt.

## Spot checks

```
git diff --name-only integration/lean-model~1...HEAD -- Graded/ | grep -v Sufficient   # empty
grep -n "join_comm" Graded/Sufficient.lean            # ideally still none
python3 scripts/laws-inventory.py --by-property        # the commutativity list, after
grep -n "Status:" docs/design.md                       # the question's status updated
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-sufficient-grade-nested -b step/sufficient-grade-nested integration/lean-model
cd ../wt-sufficient-grade-nested
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true
START=$(date +%s)
```

## Verify GREEN baseline / after

```
make all > /dev/null; echo all=$?      # must be 0, before and after
```
Regenerate `docs/laws.md` and commit it. Read `tail -n 20 build.log` only.

## Commit and merge back

```
git add -A
git commit -F- << 'MSG'
sufficient-grade-nested: the nested carriers, and the migration's account of itself

flatten is the one operation whose job is grade arithmetic, so this leg
shows what a caller-nominated grade does and does not remove. With
Comp.grade_reassoc's analogue settled, the migration can state its own
result: which structures got strictly cheaper, which traded a cast in a
statement for an argument at a call site, and what a grade must supply for
each. Closes cast-burden-migration-scope.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/sufficient-grade-nested -m "merge step/sufficient-grade-nested [sufficient-grade-nested]"
```

Stage files **by name** in the main checkout.

## Record measurements

`verify_runs` / `edit_iterations` / `proof_attempts`, as in the preceding
legs.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-sufficient-grade-nested
git branch -d step/sufficient-grade-nested
```

## Handoff

Mark `sufficient-grade-nested` done in `tmp/plan/checklist.md`. There is no
next step. Write `tmp/plan/handoff-migration-review.md` addressed to a
scoped `model: opus` review of this three-leg run — the same shape as
`INTEGRATION-REVIEW.md` served the first run, but bounded to the migration:
what the three legs cost, whether the two-layer-and-bridge design held
across all of them, every bridge's direction, and anything in
`docs/design.md` this run left provisional or open. Do not write the review
itself.
