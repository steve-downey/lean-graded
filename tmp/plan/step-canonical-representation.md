# step: canonical-representation

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

The C++ `error_set` is canonicalized so that `error_set<A,B>` and
`error_set<B,A>` are *the same type*, via an alias delegating to a
sorted detail carrier (`docs/design.md#cpp-counterpart`). This model
used Mathlib's `Finset`, which is a quotient — order-free by
construction — so nothing so far has tested the C++ mechanism. This
step does: it builds the *representation* the C++ uses (a sorted,
duplicate-free list of error kinds under a linear order) and proves it
equivalent to `Finset`, with `union` and `∅` carried across. The Lean
statement of "the same type" is an `Equiv` between the quotient and its
canonical representatives, plus the fact that `union` on
representatives is well-defined and computes the same thing. It also
surfaces the C++ requirement the model had been hiding: canonical
sorting needs a **linear order on error kinds** (C++: a total order on
types, whatever the detail carrier uses); `Finset` needed only
`DecidableEq`. That is a finding for the paper.

## What already exists

`docs/design.md#grade`, `#traverse` (tuple subsection, `joinAll_perm`).

## The change

Create `Graded/Canonical.lean`:

```lean
variable {Err : Type u} [LinearOrder Err]

/-- The C++ detail carrier: sorted, no duplicates. -/
def Canon (Err) [LinearOrder Err] := { l : List Err // l.Sorted (· < ·) }

def Canon.ofFinset : Finset Err → Canon Err   -- Finset.sort
def Canon.toFinset : Canon Err → Finset Err
```

- `canonEquiv : Finset Err ≃ Canon Err` (use `Finset.sort` and
  `List.toFinset`; Mathlib has `Finset.sort_toFinset` and
  `List.Sorted` lemmas — find the exact names, do not guess).
- `Canon.union` defined by merging (or by round-tripping through
  `Finset` — the round-trip definition is fine for the theorem;
  note it is not the C++ algorithm) and
  `canonEquiv_union : canonEquiv (join g h) = Canon.union (canonEquiv g)
  (canonEquiv h)`.
- `canon_perm : gs ~ gs' → Canon.ofList gs = Canon.ofList gs'` — the
  direct statement of "`error_set<A,B>` is `error_set<B,A>`", where
  `ofList` sorts and dedups. Cites `joinAll_perm` from [traverse-tuple]
  or reproves via `List.Perm`; prefer citing.
- `canon_requires_linear_order`: not a theorem — a docstring and a
  living-doc line stating that `Canon` needs `[LinearOrder Err]` where
  `Grade` needed `[DecidableEq Err]`, and what that corresponds to in
  C++.

No consumer change: the example stays on `Finset`. `Canon` is a
representation theorem, not a second grade — say so in the living doc
so the integration review does not read it as a fork.

### Tests

`Tests/Canonical.lean`: give `E` a `LinearOrder` (via `deriving Ord`
plus an instance, or an explicit `toNat` embedding); `decide` that
`canonEquiv {E.range, E.parse}` has the sorted list; round-trip.

### Living doc

`docs/design.md#representation`.

### Letter

`blog/letters/canonical-representation.org`, title "Two spellings, one
type: what sorting the pack actually proves". "Back in C++": the sorted
detail carrier is an implementation of `canonEquiv`; the alias template
is the `ofFinset` direction; deduction through the alias is where the
`toFinset` direction is *assumed* to be recoverable — and that is worth
a test in the C++ repo.

## Declared file scope

`Graded.lean`, `Graded/Canonical.lean`, `Tests.lean`,
`Tests/Canonical.lean`, `docs/design.md` (`#representation`),
`blog/letters/canonical-representation.org`.

## Spot checks

```
grep -n "LinearOrder" Graded/Canonical.lean
grep -rn "Canon" Graded/Grade.lean Graded/Carrier.lean     # nothing
```

## Setup

```
cd __MAIN_CHECKOUT__
git worktree add ../wt-canonical-representation -b step/canonical-representation integration/lean-model
cd ../wt-canonical-representation
ln -s __MAIN_CHECKOUT__/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-canonical-representation.md`
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
canonical-representation: Finset vs sorted duplicate-free list; the type-identity claim as an Equiv

Builds the representation the C++ actually uses and proves it
equivalent to the quotient the model used, carrying union across. It
also surfaces that canonical sorting needs a linear order on error
kinds where the model needed only decidable equality.
MSG
cd __MAIN_CHECKOUT__
git checkout integration/lean-model
git merge --no-ff step/canonical-representation -m "merge step/canonical-representation [canonical-representation]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-canonical-representation
printf '%s\n' '{"step":"canonical-representation","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/canonical-representation | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> __MAIN_CHECKOUT__/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd __MAIN_CHECKOUT__
git worktree remove --force ../wt-canonical-representation
git branch -d step/canonical-representation
```

## Handoff

Mark `canonical-representation` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-oracle-export.md`. Write `tmp/plan/handoff-oracle-export.md` fresh, per
the contract in `AGENT-PROMPT.md`.
