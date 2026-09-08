# step: compose-flatten

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

Traversable's composition law needs `Compose F G`; for graded functors
the natural grade of `Graded g (Graded h α)` is the *pair* `(g, h)` in
the product pomonoid, not the union. The C++ collapses nested
`expected<expected<T,E1>,E2>` to `expected<T, E1 ∪ E2>` and treats that
as obviously right. It is right, but it is a **distributive-law-shaped
theorem**: the flattening must be compatible with `map`, `pure`, `bind`
and `widen` in each layer. This step states the flattening and proves
those compatibilities, and it settles whether the composition law of
`traverse` holds through the flattening.

## What already exists

`docs/design.md#traverse` (`traverse`, `traverse_cons`), `#monad`
(`bind`, `bind_assoc`), `#subsumption`, `#grade`.

## The change

Create `Graded/Compose.lean`:

```lean
def flatten : Graded g (Graded h α) → Graded (Grade.join g h) α
  | .ok (.ok a)      => .ok a
  | .ok (.err e he)  => .err e (Grade.le_join_right he)
  | .err e he        => .err e (Grade.le_join_left he)
```

- `flatten_eq_bind_id : flatten x = bind x id` — flatten is `join` in the
  monad sense; this makes every later law inherit from [monad-laws].
- `flatten_map : flatten (map (map f) x) = map f (flatten x)`.
- `flatten_pure_outer : flatten (pure y) = cast _ y` (unit).
- `flatten_pure_inner : flatten (map pure x) = cast _ x` (unit).
- `flatten_flatten : flatten (flatten x) = cast (join_assoc ..) (flatten
  (map flatten x))` (associative) — the monad multiplication law.
- `flatten_widen_outer`, `flatten_widen_inner` (order): widening either
  layer then flattening = flattening then widening by `join_mono`.
- `flatten_comm : flatten x = cast (join_comm ..) (flatten (swap x))`
  where `swap : Graded g (Graded h α) → Graded h (Graded g α)` — **only
  provable when at most one layer is an error**; otherwise the surviving
  error differs. Prove the conditional form; record it as the third
  appearance of the same condition.
- Traverse composition: with `traverse` from [traverse-list],
  `traverse (fun a => map (traverse k) (f a)) xs` at grade `g` of
  `Graded h (List γ)` flattened equals `traverse (fun a => flatten
  (map k' (f a))) xs` — state the cleanest form you can get to typecheck
  in `Compose.lean` **only if** it lands in three attempts or a bounded
  `grind` loop; otherwise state it as a `theorem` with the exact
  statement and a `sorry`, **do not commit**, and write
  `blocked-compose-flatten.md` with the statement. The statement is worth
  more than a weakened proof here.

### Consumer

`Examples/Validation.lean`: a stage that returns a graded value inside
a graded value (`lookup : String → Graded {io} (Graded {parse} Nat)`),
flattened, `#guard`ed.

### Tests

`Tests/Compose.lean`.

### Living doc

`docs/design.md#compose`: product pomonoid vs union, the flattening as
monad multiplication, the conditional `flatten_comm`, status of the
composition law.

### Letter

`blog/letters/compose-flatten.org`, title "Nested expecteds and the
distributive law nobody wrote down". "Back in C++": whenever P3200's
users nest, the union is doing a `join` in the monad sense, and its
laws are these.

## Declared file scope

`Graded.lean`, `Graded/Compose.lean`, `Tests.lean`, `Tests/Compose.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#compose`),
`blog/letters/compose-flatten.org`.

## Spot checks

```
grep -n "flatten_eq_bind_id\|flatten_flatten" Graded/Compose.lean
grep -n "join_comm" Graded/Compose.lean     # only in flatten_comm
```

## Setup

```
cd __MAIN_CHECKOUT__
git worktree add ../wt-compose-flatten -b step/compose-flatten integration/lean-model
cd ../wt-compose-flatten
ln -s __MAIN_CHECKOUT__/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-compose-flatten.md`
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
compose-flatten: nested carriers, product grade, and the union-flattening laws

The C++ collapses nested expecteds to the union grade without stating
the laws that make it safe. flatten is the monad multiplication; its
compatibility with map, pure, bind and widen is proved, and the
commutation of layers is shown to hold only under the same at-most-one-
error condition found twice already.
MSG
cd __MAIN_CHECKOUT__
git checkout integration/lean-model
git merge --no-ff step/compose-flatten -m "merge step/compose-flatten [compose-flatten]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-compose-flatten
printf '%s\n' '{"step":"compose-flatten","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/compose-flatten | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> __MAIN_CHECKOUT__/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd __MAIN_CHECKOUT__
git worktree remove --force ../wt-compose-flatten
git branch -d step/compose-flatten
```

## Handoff

Mark `compose-flatten` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-graded-morphism.md`. Write `tmp/plan/handoff-graded-morphism.md` fresh, per
the contract in `AGENT-PROMPT.md`.
