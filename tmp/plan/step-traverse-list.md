# step: traverse-list

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

`traverse` is what P3200 is about. In a graded setting its grade is a
fold of the element grades over the container's shape, which for a
runtime-length `List` is not a static type unless the grade of every
element is the same `g` **and** `g ⊔ g = g`. This step proves the
theorem that makes the C++ design typeable: with a uniform element
function of grade `g`, the traversal has grade `g` regardless of length —
and it proves it with `join_idem` as the *visible* dependency, so the
paper can say "shape-independence of the traversal grade requires
idempotence" and point at a theorem. The empty list has grade ∅ and must
be lifted by `widen`; that is the second finding.

The general (non-idempotent) case is *not* modelled here; the living doc
states that as scope, not as a gap.

## What already exists

`docs/design.md#monad`, `#applicative` (`map2`), `#subsumption`
(`fromEmpty`, `widen`), `#grade` (`join_idem`, `bot_join`).

## The change

Create `Graded/Traverse.lean`:

Define the *shape-fold* grade first, honestly:
```lean
def foldGrade (g : Grade Err) : List α → Grade Err
  | []      => Grade.bot
  | _ :: xs => Grade.join g (foldGrade g xs)

def traverseRaw (f : α → Graded g β) : (xs : List α) → Graded (foldGrade g xs) (List β)
  | []      => pure []
  | x :: xs => map2 (· :: ·) (f x) (traverseRaw f xs)
```
Then the theorems:

- `foldGrade_cons_ne_nil : xs ≠ [] → foldGrade g xs = g` — **cites
  `join_idem`** (and `join_bot` for the base). This is the theorem.
- `foldGrade_nil : foldGrade g [] = bot`.
- `foldGrade_le : foldGrade g xs ⊆ g` — needs only `join_le`/`bot_le`,
  not idempotence. Note the difference: *bounded by* `g` is free;
  *equal to* `g` costs idempotence.
- `traverse (f : α → Graded g β) (xs : List α) : Graded g (List β) :=
  widen (foldGrade_le) (traverseRaw f xs)` — the public one, with a
  uniform grade. Using `widen` with `foldGrade_le` rather than `cast`
  with `foldGrade_cons_ne_nil` handles the empty list uniformly. Record
  in the living doc that this makes the *definition* need only the
  order, while the *precision* claim (the grade isn't padded) is
  `foldGrade_cons_ne_nil` and needs idempotence. That split is the
  finding.
- `traverse_nil : traverse f [] = fromEmpty []` (up to `widen_irrel`).
- `traverse_cons : traverse f (x :: xs) = cast _ (map2 (· :: ·) (f x)
  (traverse f xs))` with a `join_idem` cast.
- `traverse_map : traverse f (xs.map h) = traverse (f ∘ h) xs`.
- Identity law: `traverse (fromEmpty) xs = fromEmpty xs` at grade `g`
  (the C++ "traversing with the identity context is the identity",
  spelled through the ∅-collapse).
- `traverse_length` : the `.ok` result has the same length as `xs`
  (shape preservation, the P3200 promise).

Naturality and composition laws are [graded-morphism] and
[compose-flatten]; do not attempt them here.

### Consumer

`Examples/Validation.lean`: `traverse parseNat ["1","2","x"]` and
`["1","2","3"]`, `#guard` on both; `traverse parseNat []` compared to
`fromEmpty []`.

### Tests

`Tests/Traverse.lean`; include a `decide` that `foldGrade {E.parse}
[1,2,3] = {E.parse}` computes.

### Living doc

`docs/design.md#traverse`: definitions, the bounded-vs-equal split, the
scope statement about non-idempotent grades.

### Letter

`blog/letters/traverse-list.org`, title "Why the error set doesn't grow
with the vector". Explain to the C++ reader that their `traverse` type
signature is only writable because unions are idempotent, and that the
model separates "won't exceed" (free) from "exactly" (idempotence).

## Declared file scope

`Graded.lean`, `Graded/Traverse.lean`, `Tests.lean`, `Tests/Traverse.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#traverse`),
`blog/letters/traverse-list.org`.

## Spot checks

```
grep -n "join_idem" Graded/Traverse.lean          # in foldGrade_cons_ne_nil and traverse_cons only
grep -n "def traverse " Graded/Traverse.lean       # one public traverse
```

## Setup

```
cd __MAIN_CHECKOUT__
git worktree add ../wt-traverse-list -b step/traverse-list integration/lean-model
cd ../wt-traverse-list
ln -s __MAIN_CHECKOUT__/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-traverse-list.md`
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
traverse-list: traverse over List; grade shape-independent by idempotence; empty via widen

Separates the free fact (traversal grade is bounded by g, needs only
the order) from the costly one (it equals g, needs join_idem). That
split is what lets the paper state precisely why the C++ traverse
signature is writable for error_set and would not be for a counting
grade.
MSG
cd __MAIN_CHECKOUT__
git checkout integration/lean-model
git merge --no-ff step/traverse-list -m "merge step/traverse-list [traverse-list]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-traverse-list
printf '%s\n' '{"step":"traverse-list","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/traverse-list | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> __MAIN_CHECKOUT__/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd __MAIN_CHECKOUT__
git worktree remove --force ../wt-traverse-list
git branch -d step/traverse-list
```

## Handoff

Mark `traverse-list` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-traverse-tuple.md`. Write `tmp/plan/handoff-traverse-tuple.md` fresh, per
the contract in `AGENT-PROMPT.md`.
