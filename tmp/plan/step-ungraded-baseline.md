# step: ungraded-baseline

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

Added 2026-09-08, after the original plan. It is not a detour: it
supplies the comparison column without which the model's headline table
cannot be read.

## Why

Every step so far has recorded which pomonoid property each law
consumes. That table has one column, and it silently conflates two
different quantities: **what a monad/applicative/traversal law costs at
all**, and **what grading adds on top**. A reader — or a paper — cannot
tell them apart from what is currently written down. The ungraded
baseline is the second column.

There is direct evidence this matters. [compose-flatten] refuted a
composition law and the result was briefly recorded as though graded
traversable composition had failed. It had not: the counterexample
survives with grading switched off entirely
([graded-traversable-composition](../../docs/design.md#graded-traversable-composition)).
A baseline would have caught that at the time, because the refutation
would have appeared in the ungraded column too.

This is cheaper than it sounds, for two reasons.

**Mathlib already has the ungraded carrier.** `LawfulTraversable (Sum σ)`
is proved in `Mathlib/Control/Traversable/Instances.lean` — `σ ⊕ α` is
error-or-value, the ungraded shape of `Graded g α` — with `id_traverse`,
`comp_traverse`, `traverse_eq_map_id` and `naturality`. Nothing here
needs re-deriving; what is missing is the *correspondence*.

**The ungraded gadget is already inside the graded one.** Fix a single
grade `g` and every `join g g` collapses by `Grade.join_idem`, every
`cast` becomes `rfl`, and what remains is the ordinary monad. That is the
sentence the paper wants: *the ungraded monad is the graded monad at a
single idempotent grade* — which is exactly why C++ code with one error
type can behave as though the grade were not there. Note the collapse
needs idempotence specifically: a third place `join_idem` earns its
keep, after [traverse-list] and [traverse-tuple].

## What already exists

`docs/design.md#grade`, `#carrier`, `#monad`, `#applicative`,
`#subsumption` (`fromEmpty`), `#traverse`, `#compose`, `#morphisms`.
All the laws whose costs this step is measuring.

## The change

Create `Graded/Ungraded.lean`.

### 1. The fixed-grade specialization

```lean
variable {Err : Type u} [DecidableEq Err] {g : Grade Err}

/-- The carrier at one fixed grade. Not a new type: a reading of the
    existing one with the grade held still. -/
abbrev Fixed (g : Grade Err) (a : Type u) : Type u := Graded g a

/-- `pure` into a fixed grade goes through the empty-collapse and widens
    — `fromEmpty` from [subsumption-widen], reused, not redefined. -/
def pureF (a : A) : Fixed g A := fromEmpty a

/-- `bind` at one grade: the union `g` join `g` collapses by idempotence. -/
def bindF (x : Fixed g A) (f : A -> Fixed g B) : Fixed g B :=
  cast (Grade.join_idem g) (bind x f)
```

and `apF`, `map2F` the same way. **`traverse` needs no specialization**:
it is already uniform-grade by construction ([traverse-list] defined it
through `widen`, not `cast`). Say so rather than writing a `traverseF`.

### 2. The ordinary laws, with no grade arithmetic in sight

- `bindF_pure_left : bindF (pureF a) f = f a`
- `bindF_pure_right : bindF x pureF = x`
- `bindF_assoc : bindF (bindF x f) k = bindF x (fun a => bindF (f a) k)`
- the four `apF_*` laws, likewise cast-free in their statements.

These are the ungraded monad and applicative laws verbatim — no `cast`,
no `join`, nothing about grades in any statement. **That absence is the
result.** Record, for each law, which pomonoid properties are still
needed in the *proof* even though none appear in the *statement*. The
difference between the two lists is precisely what grading adds, and it
is the second column of the inventory.

### 3. The correspondence with Mathlib

Give the transport to Mathlib's ungraded carrier: a function from
`Fixed g A` to the sum of `{ e : Err // e in g }` and `A`, and an
`Equiv` between them; then show `bindF`/`pureF` correspond to `Sum`'s
(or `Except`'s) own.

**Bound this**: if the transport lands in three attempts, prove it. If
it does not, state the correspondence as a documented statement-by-
statement table in the living doc instead and say which you did. A table
comparing our four traversal laws against `LawfulTraversable`'s
`id_traverse` / `comp_traverse` / `traverse_eq_map_id` / `naturality`
fields is worth having either way; the proved transport is a bonus, not
the deliverable.

Where a law of ours has **no** Mathlib counterpart, or Mathlib has one we
never stated, say so. A missing row in either direction is a finding.

### 4. The row that would have caught the conflation

Check the flattened composition law at a fixed grade — the statement
[compose-flatten] refuted:

```lean
flatten (map (traverse k) (traverse f xs)) = traverse (fun a => flatten (map k (f a))) xs
```

It fails here too. Record it in the table as: *fails ungraded, fails
graded, therefore not a fact about grading*. Contrast it, in the same
table, with Mathlib's `comp_traverse`, which keeps the two layers
separate under `Comp.mk` and **holds** for `Sum`-shaped carriers — a
different statement, whose graded form [compose-applicative] tests. Those
two rows side by side are the clearest statement of the distinction the
project had to learn the hard way.

### 5. The obligations summary

Fill the living doc with the two-column table for every law in the
model: *what the law costs ungraded* against *what grading adds*. This is
the summary [oracle-export] mechanizes, so keep the law names exactly as
they appear in `Graded/*.lean`.

### Consumer

**None.** The examples stay as they are; `Examples/Validation.lean` is
not in this step's declared scope. Do not add one.

### Tests

`Tests/Ungraded.lean`: each fixed-grade law at `E`; a `#guard` that
computes; the flattened-composition counterexample at a single grade,
executable, so the "fails ungraded" claim is checked and not asserted.

### Living doc

New anchor `## ungraded-baseline`, placed immediately before
`## laws-inventory`. Note: this raises the top-level anchor count from 14
to 15. [baseline-capture]'s spot check expects 14 and is historical;
do not "fix" the doc back.

### Letter

`blog/letters/ungraded-baseline.org`, title "What grading actually
costs". This is the letter for a C++ reader who has been waiting to know
whether any of this was worth it: show one law in its ordinary form and
then in its graded form, and let the difference be the answer. "Back in
C++": with a single error type the grade is invisible and every law you
already believed still holds; the grade only starts costing you where
two different error sets meet, and the cost is exactly the properties in
the second column.

## Declared file scope

`Graded.lean`, `Graded/Ungraded.lean`, `Tests.lean`,
`Tests/Ungraded.lean`, `docs/design.md` (`#ungraded-baseline`),
`blog/letters/ungraded-baseline.org`.

## Spot checks

```
grep -c "cast" Graded/Ungraded.lean
grep -n "join_idem" Graded/Ungraded.lean
grep -n "comp_traverse\|LawfulTraversable" docs/design.md
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-ungraded-baseline -b step/ungraded-baseline integration/lean-model
cd ../wt-ungraded-baseline
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

Mathlib's `Sum`/`Traversable` material is under
`Mathlib/Control/Traversable/`. Read the real definitions there before
citing them; do not guess lemma or field names.

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-ungraded-baseline.md`
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
ungraded-baseline: the comparison column — what a law costs, and what grading adds

Every law's recorded cost until now conflated what the law needs at all
with what grading adds on top. Fixing one grade collapses every join by
idempotence and every cast to rfl, leaving the ordinary laws with no
grade arithmetic in their statements; the properties still needed in
their proofs are exactly what grading costs. Mathlib's LawfulTraversable
for Sum gives an independent check that these were the right statements
to prove, and the flattened composition law failing here too is the row
that would have caught an earlier misreading.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/ungraded-baseline -m "merge step/ungraded-baseline [ungraded-baseline]"
```

Stage your files **by name** for anything committed in the main checkout;
do not use `git add -A` there. See your inbound handoff.

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-ungraded-baseline
printf '%s\n' '{"step":"ungraded-baseline","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/ungraded-baseline | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-ungraded-baseline
git branch -d step/ungraded-baseline
```

## Handoff

Mark `ungraded-baseline` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-grade-obligations.md`. Write `tmp/plan/handoff-grade-obligations.md` fresh, per
the contract in `AGENT-PROMPT.md`. It abstracts the obligations your
two-column table records, so it needs that table's exact law names and
which properties each proof actually used.
