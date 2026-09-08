# step: graded-carrier

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

The C++ carrier is `expected<T, error_set<Es...>>`: a value, or **one**
error whose type is in the set (`docs/design.md#cpp-counterpart`). At
grade ∅ the C++ carrier is bare `T` — a different type. This step models
the carrier and immediately tests the ∅-decision by asking Lean the honest
question: is `Graded ∅ α` *the same as* `α`, or merely *isomorphic to* it?
It can only be the latter (they are different inductive types), and the
proof of the `Equiv` is one line because the error constructor is
uninhabited at ∅. That is the letter.

This step also introduces the **consumer** every later step exercises:
a two-stage validation (`parseInt : String → Graded {parse} Nat`,
`checkRange : Nat → Graded {range} Nat`). Defining the carrier without a
consumer in the same step would leave its shape unexamined until
[monad-laws]; the example is what makes a wrong constructor choice visible
now.

## What already exists

`Graded.Grade` — `docs/design.md#grade` for the lemma names.

## The change

Create `Graded/Carrier.lean` (import in `Graded.lean`):

```lean
import Graded.Grade
namespace Graded
variable {Err : Type u} [DecidableEq Err]

/-- A value of type `α`, or one error `e` together with the evidence that
    `e`'s kind belongs to the grade `g`. -/
inductive Graded (g : Grade Err) (α : Type v)
  | ok  : α → Graded g α
  | err : (e : Err) → e ∈ g → Graded g α
```

Then:

- `map : (α → β) → Graded g α → Graded g β`, with `map_id` and `map_comp`.
  Note in a comment and in the living doc: **the grade does not appear
  in `map`'s type** — this is the "functors are oblivious to grading"
  fact, and it is true by construction, not by proof.
- `emptyEquiv : Graded (Grade.bot : Grade Err) α ≃ α`. The `err` case is
  eliminated by `Finset.not_mem_empty`. Prove also
  `map_emptyEquiv : emptyEquiv (map f x) = f (emptyEquiv x)` (naturality
  of the ∅-collapse — this is what "bare `T` is safe" means).
- `cast (h : g = g') : Graded g α → Graded g' α` by `h ▸`, plus
  `cast_rfl : cast rfl x = x` and `cast_cast`. Later steps state laws
  "modulo grade equalities" through this; introduce it here so
  [monad-laws] doesn't invent it. `docs/design.md#carrier` records it as
  **provisional**: "Laws are stated with exact union grades and `cast`,
  mirroring C++ where `bind` computes the union type. The alternative —
  `bind` at any sufficient grade `k` with `g ∪ h ⊆ k`, absorbing
  subsumption — would remove every `cast`. Revisit if [monad-laws] or
  [traverse-list] finds the casts dominate the proofs."
- `DecidableEq (Graded g α)` given `DecidableEq α` and `DecidableEq Err`;
  the proof-of-membership component is a `Prop`, so this is proof-
  irrelevant — say so in the letter (C++ variant equality ignores the
  "which alternatives exist" part the same way).

### The consumer

`Examples/Validation.lean` (import in `Examples.lean`):

```lean
inductive E | parse | range | io deriving DecidableEq, Repr
def parseNat (s : String) : Graded ({E.parse} : Grade E) Nat := ...
def checkRange (n : Nat) : Graded ({E.range} : Grade E) Nat := ...
```
Using `String.toNat?`. Compose them **by hand** with a `match` — no `bind`
yet — producing `Graded {E.parse, E.range} Nat`, and `#eval` it on a good,
an unparsable, and an out-of-range input. The hand-written composition is
the thing [monad-laws] replaces; leave a comment `-- REPLACED-BY: bind`
on it.

### Tests

`Tests/Carrier.lean`: `map_id`/`map_comp` at `E`; `emptyEquiv` round-trips
on `Graded.ok 3` with `decide`/`rfl`; a `#guard` on the example.

### Letter

`blog/letters/graded-carrier.org`, title "The empty grade is not bare T,
but it might as well be". Core of the letter: the `Equiv` proof, and
why "isomorphic" is the *stronger* statement to be able to make than
"same type" — it says the two representations agree on every operation,
which C++'s implicit conversion asserts without proof.

## Declared file scope

`Graded.lean`, `Graded/Carrier.lean`, `Tests.lean`, `Tests/Carrier.lean`,
`Examples.lean`, `Examples/Validation.lean`, `docs/design.md` (`#carrier`
and one line in `#provisional-decisions`), `blog/letters/graded-carrier.org`.

## Spot checks

```
grep -n "emptyEquiv\|REPLACED-BY" Graded/Carrier.lean Examples/Validation.lean
grep -n "Provisional" docs/design.md | grep -i cast
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-graded-carrier -b step/graded-carrier integration/lean-model
cd ../wt-graded-carrier
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-graded-carrier.md`
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
graded-carrier: carrier holding one in-grade error; empty-grade Equiv; first consumer

Models expected<T, error_set<Es...>> and settles the bare-T-at-empty
decision as an isomorphism rather than an identity, which is the
strongest honest statement. The validation example is introduced now so
the carrier shape is tested by a consumer immediately.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/graded-carrier -m "merge step/graded-carrier [graded-carrier]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-graded-carrier
printf '%s\n' '{"step":"graded-carrier","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/graded-carrier | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-graded-carrier
git branch -d step/graded-carrier
```

## Handoff

Mark `graded-carrier` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-subsumption-widen.md`. Write `tmp/plan/handoff-subsumption-widen.md` fresh, per
the contract in `AGENT-PROMPT.md`.
