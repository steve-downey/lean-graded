# step: traverse-tuple

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

P3200's other shape is the tuple: a heterogeneous product whose elements
carry *different* grades. There the fold of grades is static — a
type-level union of the element grades — and no idempotence is needed
for it to be typeable, only for it to be *tidy*. This is the C++
`transpose(tuple<expected<A, error_set<X>>, expected<B,
error_set<Y>>>)` → `expected<tuple<A,B>, error_set<X,Y>>` case. It is
also where the C++ canonicalization does real work (`error_set<X,Y>`
must equal `error_set<Y,X>`), which [canonical-representation] picks up.

## What already exists

`docs/design.md#traverse` (`foldGrade` pattern, `map2`), `#applicative`,
`#grade` (`join_assoc`, `join_comm`).

## The change

Create `Graded/Tuple.lean`. Represent a heterogeneous tuple of graded
values as an `HList` indexed by a list of `(Grade Err × Type)` pairs, or
— simpler and sufficient — as a dependent list indexed by the list of
grades with a uniform payload type first, then generalize only if the
uniform version is trivial:

```lean
inductive GList : (gs : List (Grade Err)) → (αs : List (Type v)) → Type _
  | nil  : GList [] []
  | cons : Graded g α → GList gs αs → GList (g :: gs) (α :: αs)

def joinAll : List (Grade Err) → Grade Err := List.foldr Grade.join Grade.bot

def sequence : GList gs αs → Graded (joinAll gs) (HList αs)
```
(`HList` from Mathlib or a local three-line definition — check what
Mathlib provides under the pinned version before writing one; if you
write one, it is a shared definition and goes in `Graded/Prelude.lean`,
declared in the handoff.)

Theorems:

- `joinAll_perm : gs ~ gs' → joinAll gs = joinAll gs'` — **cites
  `join_comm` and `join_assoc`**. This is the tuple-order-independence
  fact; C++ gets it from type canonicalization. Note it does **not**
  need idempotence.
- `joinAll_dedup : joinAll (gs.dedup) = joinAll gs` — needs
  `join_idem`. Tidiness, not typeability.
- `sequence_nil : sequence .nil = pure .nil`.
- `sequence_cons : sequence (.cons x xs) = map2 HList.cons x (sequence xs)`.
- Shape preservation is by construction (the index `αs` is unchanged);
  say so in the living doc rather than proving a trivial theorem.

### Consumer

`Examples/Validation.lean`: `sequence` of a 3-tuple `(parseNat s,
checkRange n, logIt n)` with grades `{parse}`, `{range}`, `{io}`; the
result grade must be displayed by `#check` as the union; `#guard` on a
success and on a failure in the middle element.

### Tests

`Tests/Tuple.lean`; `decide` that `joinAll [{E.parse},{E.range}] =
joinAll [{E.range},{E.parse}]`.

### Living doc

`docs/design.md#traverse`: tuple subsection; the property table now
has two rows for order-independence (comm+assoc) and dedup (idem).

### Letter

`blog/letters/traverse-tuple.org`, title "Tuples are where the grade is
really computed". "Back in C++": the tuple case is the one where
`error_set<X,Y>` ≡ `error_set<Y,X>` is load-bearing, and the theorem
that licenses it is commutativity plus associativity — not the
canonical sorting, which is an *implementation* of the theorem.

## Declared file scope

`Graded.lean`, `Graded/Tuple.lean`, `Graded/Prelude.lean` (only if an
`HList` is needed), `Tests.lean`, `Tests/Tuple.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#traverse`),
`blog/letters/traverse-tuple.org`.

## Spot checks

```
grep -n "joinAll_perm\|joinAll_dedup" Graded/Tuple.lean
grep -n "join_idem" Graded/Tuple.lean      # only in joinAll_dedup
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-traverse-tuple -b step/traverse-tuple integration/lean-model
cd ../wt-traverse-tuple
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-traverse-tuple.md`
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
traverse-tuple: heterogeneous sequence over a graded tuple; static join; order-independence

The tuple case is where the grade is computed at the type level. Order
independence of the joined grade needs commutativity and associativity
only; dedup needs idempotence. C++ canonical sorting is an
implementation of the first theorem, and the model keeps the two apart.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/traverse-tuple -m "merge step/traverse-tuple [traverse-tuple]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-traverse-tuple
printf '%s\n' '{"step":"traverse-tuple","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/traverse-tuple | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-traverse-tuple
git branch -d step/traverse-tuple
```

## Handoff

Mark `traverse-tuple` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-compose-flatten.md`. Write `tmp/plan/handoff-compose-flatten.md` fresh, per
the contract in `AGENT-PROMPT.md`.
