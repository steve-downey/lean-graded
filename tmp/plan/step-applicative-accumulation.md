# step: applicative-accumulation

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

The classic non-monad applicative is Validation: combine independent
checks and keep *all* their errors. The theory question the C++ design
has not answered: does an accumulating instance share the carrier? The
plan's prediction is **no**: `Graded g α` holds exactly one error
([graded-carrier]), so an accumulating `ap` has nowhere to put the
second. That means either (a) a second carrier `Accum g α` holding a
non-empty list of in-grade errors, with the *same grade* and a
grade-preserving morphism `Accum g α → Graded g α` (take the first), or
(b) the prediction is wrong and there is a way to accumulate in the
existing carrier — in which case the design changed and this step is an
amendment. This step is written for (a). If you find (b), halt with
`amendment-applicative-accumulation.md`; do not build (a) anyway.

This is not a fork of `Graded`: `Accum` is a different structure with a
different law set, connected by a morphism, and both are recorded in
the living doc. The distinction from a nonce fork is that `Accum` never
replaces `Graded` anywhere and every step after this still uses
`Graded`.

## What already exists

`docs/design.md#applicative` (`ap`, `map2`, laws, the `ap_flip`
finding), `#carrier`, `#grade`.

## The change

Create `Graded/Accum.lean`:

```lean
inductive Accum (g : Grade Err) (α : Type v)
  | ok   : α → Accum g α
  | errs : (es : List Err) → es ≠ [] → (∀ e ∈ es, e ∈ g) → Accum g α
```
(a `Multiset` is the mathematically right thing; a `List` with a
non-emptiness proof is the computable one — pick `List` and note the
choice as provisional.)

- `Accum.pure : α → Accum bot α`; `Accum.map`; `Accum.ap` that
  *concatenates* error lists when both sides fail, at grade
  `join g h` — the membership proof for the concatenation uses
  `le_join_left`/`le_join_right`, nothing more.
- The four applicative laws for `Accum`, same names prefixed `Accum.`,
  each citing its property. Expect identity/homomorphism/composition to
  need only unit/assoc, and interchange to need the same as in
  [applicative-from-monad] — confirm.
- `Accum.notMonad`: there is no `bind : Accum g α → (α → Accum h β) →
  Accum (join g h) β` whose derived `ap` equals `Accum.ap`. Prove the
  weakest honest form: exhibit `f x` where any `bind`-derived `ap` must
  short-circuit (the second computation is never run when the first
  fails, so its errors cannot appear) while `Accum.ap` reports both.
  State it as a concrete `¬ ∃ bind, ...` at `E` if the general form is
  too heavy; write in the living doc which form landed.
- `Accum.toGraded : Accum g α → Graded g α` (first error), and
  `toGraded_grade : toGraded (Accum.ap f x) = ap (toGraded f) (toGraded x)`
  **fails in general** — prove the one-sided version: it holds when at
  most one side fails, matching [applicative-from-monad]'s `ap_flip`
  condition. Record that these two conditions are the same condition.
- `Accum.sameGrade`: stated informally in the living doc — both
  instances are indexed by the same `Grade` and the same `join`; the
  theorem is the *types* of `Accum.ap` and `ap`, side by side.

### Consumer

`Examples/Validation.lean`: `Accum` versions of `parseNat`, run the
two-field form with both fields bad, `#guard` both errors present.

### Tests

`Tests/Accum.lean` as above.

### Living doc

`docs/design.md#applicative`: add the `Accum` subsection: why a second
carrier, the morphism, the shared condition. Provisional: `List` vs
`Multiset`.

### Letter

`blog/letters/applicative-accumulation.org`, title "Same grade, twice as
many errors". "Back in C++": `expected` cannot accumulate; if the
committee ever asks for a Validation-like `traverse`, it is a different
carrier with the same `error_set` grade, and the paper can now say so
with the exact condition under which the two agree.

## Declared file scope

`Graded.lean`, `Graded/Accum.lean`, `Tests.lean`, `Tests/Accum.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#applicative`,
`#provisional-decisions`), `blog/letters/applicative-accumulation.org`.

## Spot checks

```
grep -n "notMonad\|toGraded" Graded/Accum.lean
grep -rn "Accum" Graded/Monad.lean Graded/Widen.lean    # nothing — Accum touches no earlier module
```

## Setup

```
cd __MAIN_CHECKOUT__
git worktree add ../wt-applicative-accumulation -b step/applicative-accumulation integration/lean-model
cd ../wt-applicative-accumulation
ln -s __MAIN_CHECKOUT__/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-applicative-accumulation.md`
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
applicative-accumulation: accumulating applicative needs its own carrier; same grade, not a monad

Tests whether Validation-style accumulation can share the one-error
carrier. It cannot; Accum holds a non-empty error list at the same
grade, and the condition under which the two applicatives agree is the
same condition found for ap_flip. This is design evidence for P3200,
not a fork: Accum replaces Graded nowhere.
MSG
cd __MAIN_CHECKOUT__
git checkout integration/lean-model
git merge --no-ff step/applicative-accumulation -m "merge step/applicative-accumulation [applicative-accumulation]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-applicative-accumulation
printf '%s\n' '{"step":"applicative-accumulation","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/applicative-accumulation | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> __MAIN_CHECKOUT__/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd __MAIN_CHECKOUT__
git worktree remove --force ../wt-applicative-accumulation
git branch -d step/applicative-accumulation
```

## Handoff

Mark `applicative-accumulation` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-traverse-list.md`. Write `tmp/plan/handoff-traverse-list.md` fresh, per
the contract in `AGENT-PROMPT.md`.
