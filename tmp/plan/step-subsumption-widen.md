# step: subsumption-widen

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

In C++ a narrower carrier converts implicitly to a wider one
(`docs/design.md#cpp-counterpart`). That conversion is the *order* half of
the pomonoid, and it is the part the theory papers wave at: a graded monad
over a *partially ordered* monoid needs, for each `g ⊆ g'`, a map
`F_g → F_g'` that is the identity at `g = g`, composes along `⊆`, and is
natural in the payload. Nothing in the C++ says these hold; they are true
of `expected` conversion by inspection, but nobody inspected. This step
states them and proves them, and — the part with teeth — proves that
widening commutes with the ∅-collapse from [graded-carrier], because the
letter-to-C++ claim "you can pass a bare `T` where a graded value is
expected" is exactly `widen (bot_le) ∘ emptyEquiv.symm`.

Later steps use `widen` in one specific place: the empty traversal
([traverse-list]) has grade ∅ and must be lifted to the function's grade.

## What already exists

`docs/design.md#grade` (lemma names, in particular `le_refl'`,
`le_trans'`, `bot_le`), `docs/design.md#carrier` (`Graded`, `map`,
`emptyEquiv`, `cast`).

## The change

Create `Graded/Widen.lean` (import in `Graded.lean`):

```lean
def widen (h : g ⊆ g') : Graded g α → Graded g' α
  | .ok a     => .ok a
  | .err e he => .err e (h he)
```

Theorems, with the pomonoid lemma each cites in parentheses:

- `widen_refl : widen (Grade.le_refl' g) x = x`
- `widen_widen : widen h₂ (widen h₁ x) = widen (Grade.le_trans' h₁ h₂) x`
- `widen_map : widen h (map f x) = map f (widen h x)` (naturality)
- `widen_irrel : widen h x = widen h' x` for any two proofs (proof
  irrelevance — say in the living doc that this is what makes "the
  conversion path doesn't matter" a theorem instead of a convention)
- `widen_cast : widen h (cast e x) = widen (e ▸ h) x` — the interaction
  of the two ways of changing a grade; expect this to be fiddly and give
  it a bounded `grind` loop if three attempts don't land it
- `fromEmpty : α → Graded g α := widen Grade.bot_le ∘ emptyEquiv.symm`,
  with `fromEmpty_eq_ok : fromEmpty a = .ok a` by `rfl` or `simp`.

### Consumer

In `Examples/Validation.lean`, add a third stage `logIt : Nat →
Graded {E.io} Unit` and show a value of grade `{E.parse}` widened into
`{E.parse, E.range, E.io}` compared with `decide` to the same value
constructed directly. Leave the hand-written `match` composition alone.

### Tests

`Tests/Widen.lean`: each theorem at `E`; a `#guard` that
`widen _ (.ok 3) = .ok 3` at concrete grades.

### Living doc

`docs/design.md#subsumption`: the four laws, and the sentence "subsumption
is a *functor* from the poset `(Grade, ⊆)` to endofunctors — the C++
conversion sequence is required to satisfy this and does, by these
theorems."

### Letter

`blog/letters/subsumption-widen.org`, title "Implicit conversion is a
functor, and Lean made me say so". "Refused": likely `widen_cast` — write
about what it was like to have a proof obligation for something C++ treats
as obviously fine, and whether it *was* obviously fine.

## Declared file scope

`Graded.lean`, `Graded/Widen.lean`, `Tests.lean`, `Tests/Widen.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#subsumption`),
`blog/letters/subsumption-widen.org`.

## Spot checks

```
grep -n "theorem widen_" Graded/Widen.lean | wc -l    # ≥ 5
grep -n "le_trans'\|le_refl'\|bot_le" Graded/Widen.lean # each cited
```

## Setup

```
cd __MAIN_CHECKOUT__
git worktree add ../wt-subsumption-widen -b step/subsumption-widen integration/lean-model
cd ../wt-subsumption-widen
ln -s __MAIN_CHECKOUT__/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-subsumption-widen.md`
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
subsumption-widen: widen along grade inclusion; identity, composition, naturality, empty-collapse

The C++ implicit conversion between error_set carriers is the order
half of the pomonoid. Nobody had stated that it is functorial and
natural; these theorems do, and fromEmpty makes the bare-T handoff a
proved composite instead of an assumed conversion.
MSG
cd __MAIN_CHECKOUT__
git checkout integration/lean-model
git merge --no-ff step/subsumption-widen -m "merge step/subsumption-widen [subsumption-widen]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-subsumption-widen
printf '%s\n' '{"step":"subsumption-widen","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/subsumption-widen | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> __MAIN_CHECKOUT__/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd __MAIN_CHECKOUT__
git worktree remove --force ../wt-subsumption-widen
git branch -d step/subsumption-widen
```

## Handoff

Mark `subsumption-widen` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-monad-laws.md`. Write `tmp/plan/handoff-monad-laws.md` fresh, per
the contract in `AGENT-PROMPT.md`.
