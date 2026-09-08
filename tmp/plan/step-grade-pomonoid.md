# step: grade-pomonoid

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

The grade is the whole design. The C++ side has `error_set<Es...>`: a set of
types, joined by union, ordered by inclusion, with ∅ as unit
(`docs/design.md#cpp-counterpart`). Every later law will need *some* of
the properties of that structure — associativity and unit for the monad
laws, commutativity for "applicative = monad", idempotence for
"traversal grade doesn't depend on length". The point of this model is to
find out exactly which law needs which. That is only recoverable if each
property is a **separately named theorem** from the start and every later
proof cites it by name (see `docs/RULES.md`, hypothesis discipline).

This step is deliberately thin — a horizontal layer — because the
consumer arrives one step later ([graded-carrier]) and depends on nothing
but these names.

## What already exists

`Graded/Prelude.lean` with the `Graded` namespace and a `Finset` import
(`docs/design.md#toolchain` for the import the previous step settled on).

## The change

Create `Graded/Grade.lean`; add `import Graded.Grade` to `Graded.lean`.

```lean
import Graded.Prelude
namespace Graded

/-- A grade is a finite set of error *kinds*. `Err` plays the role of the
    universe of C++ error types; `DecidableEq` is what lets us form sets. -/
abbrev Grade (Err : Type u) [DecidableEq Err] := Finset Err

namespace Grade
variable {Err : Type u} [DecidableEq Err]

def bot : Grade Err := ∅
def join (g h : Grade Err) : Grade Err := g ∪ h
-- order is `⊆`, written `g ≤ h` via Finset's PartialOrder; state the
-- lemmas below against `⊆` so C++ readers see "subset".
```

Then the **named property lemmas**, one each, with exactly these names.
Each is a one-line appeal to the Mathlib `Finset` lemma, but the name is
the deliverable:

- `join_assoc : join (join g h) k = join g (join h k)`
- `join_comm : join g h = join h g`
- `join_idem : join g g = g`
- `bot_join : join bot g = g` and `join_bot : join g bot = g`
- `le_join_left : g ⊆ join g h` and `le_join_right : h ⊆ join g h`
- `join_le : g ⊆ k → h ⊆ k → join g h ⊆ k`
- `join_mono : g ⊆ g' → h ⊆ h' → join g h ⊆ join g' h'`
- `le_refl' : g ⊆ g`, `le_trans' : g ⊆ h → h ⊆ k → g ⊆ k`
- `bot_le : bot ⊆ g`
- `join_eq_right_of_le : g ⊆ h → join g h = h`

Mark `join_comm` and `join_idem` with a docstring line
`/-- PROPERTY: commutative -/`, `/-- PROPERTY: idempotent -/`; likewise
`PROPERTY: associative`, `PROPERTY: unit`, `PROPERTY: order`. Those tags
are what [oracle-export] greps.

Do **not** register the pomonoid as a Mathlib class instance
(`SemilatticeSup`, `OrderedCommMonoid`) yet. Later steps must be able to
see which of these lemmas they used; a typeclass would hide that behind
`simp`. Record this as provisional in `docs/design.md#grade`: "Not an
instance, so that lemma use stays greppable. Revisit if a later step needs
Mathlib's lattice API for a proof that is otherwise long."

### Tests

`Tests/Grade.lean` (import into `Tests.lean`): with
`inductive E | parse | range | io deriving DecidableEq, Repr`,
`#guard join {E.parse} {E.range} = join {E.range} {E.parse}` computes via
`decide`; an `example` instantiating each lemma.

### Living doc

Fill `docs/design.md#grade`: the definition, the list of lemma names, the
PROPERTY tag convention, the provisional note above.

### Letter

`blog/letters/grade-pomonoid.org`, title "The grade is a set, and every
fact about it gets a name". "Refused" section: whatever Lean actually
refused — expect the `Finset` decidability requirement to be the thing
that surprised, and explain `DecidableEq` as "the compiler needs to be
able to tell two errors apart, and in C++ that's free because types are
distinct by construction". "Back in C++": the C++ `error_set` never states
which of these properties it relies on; list the five tags and say the
rest of the series will attach laws to them.

## Declared file scope

`Graded.lean`, `Graded/Grade.lean`, `Tests.lean`, `Tests/Grade.lean`,
`docs/design.md` (`#grade` only), `blog/letters/grade-pomonoid.org`.

## Spot checks

```
grep -c "PROPERTY:" Graded/Grade.lean      # 5 or more
grep -n "instance" Graded/Grade.lean       # nothing
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-grade-pomonoid -b step/grade-pomonoid integration/lean-model
cd ../wt-grade-pomonoid
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-grade-pomonoid.md`
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
grade-pomonoid: grade as Finset with one named lemma per pomonoid property

Every later law will cite these by name so the model can report which
property each law depends on. Deliberately not a Mathlib lattice instance:
an instance would let simp use the properties invisibly, which defeats
the purpose of the model.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/grade-pomonoid -m "merge step/grade-pomonoid [grade-pomonoid]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-grade-pomonoid
printf '%s\n' '{"step":"grade-pomonoid","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/grade-pomonoid | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-grade-pomonoid
git branch -d step/grade-pomonoid
```

## Handoff

Mark `grade-pomonoid` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-graded-carrier.md`. Write `tmp/plan/handoff-graded-carrier.md` fresh, per
the contract in `AGENT-PROMPT.md`.
