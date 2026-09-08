# step: monad-laws

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

This is the centre of the model. C++ `bind` produces the union grade
(`docs/design.md#cpp-counterpart`); the three monad laws then hold only
"up to" grade equalities — `∅ ∪ h = h`, `g ∪ ∅ = g`, `(g ∪ h) ∪ k =
g ∪ (h ∪ k)` — which C++ never states because the types just come out
equal after canonicalization. In Lean they do not come out equal
definitionally; they come out *provably* equal, and the laws are stated
through `Graded.cast` ([graded-carrier], provisional decision). This
step will tell us whether that decision survives contact: if every law
proof is 80% cast-shuffling, the amendment path is the
"bind-at-sufficient-grade" alternative recorded at
`docs/design.md#carrier`.

The example composition written by hand in [graded-carrier] is replaced
by `bind` here — the consumer that validates the signature.

## What already exists

`docs/design.md#grade` (`bot_join`, `join_bot`, `join_assoc`),
`#carrier` (`Graded`, `cast`, `cast_rfl`, `cast_cast`), `#subsumption`.

## The change

Create `Graded/Monad.lean`:

```lean
def pure (a : α) : Graded (Grade.bot : Grade Err) α := .ok a

def bind (x : Graded g α) (f : α → Graded h β) : Graded (Grade.join g h) β :=
  match x with
  | .ok a     => widen Grade.le_join_right (f a)
  | .err e he => .err e (Grade.le_join_left he)
```

Note `bind` uses `widen` on the success path and `le_join_left` on the
error path; both come from [grade-pomonoid] and neither needs
commutativity. Record that observation in `docs/design.md#monad`; it is
the first line of the laws inventory.

Theorems (each cites its property):

- `bind_pure_left : bind (pure a) f = cast (Grade.bot_join h).symm (f a)`
  — hold on: check the direction of `cast`; state whichever direction
  makes the statement typecheck without extra `symm` at use sites, and
  say in the living doc which you chose and why. (unit)
- `bind_pure_right : bind x pure = cast (Grade.join_bot g).symm x` (unit)
- `bind_assoc : bind (bind x f) k = cast (Grade.join_assoc g h j).symm
  (bind x (fun a => bind (f a) k))` (associative)
- `bind_map : bind x (pure ∘ f) = cast _ (map f x)` — `map` is derivable
  from `bind`, at grade `g ∪ ∅`; this is the theorem that says the
  functor is the monad's functor. (unit)
- `bind_widen : bind (widen h₁ x) f = widen (Grade.join_mono h₁ le_refl') (bind x f)`
  — subsumption commutes with `bind`; the C++ relies on this every time a
  narrow value is passed to a wider continuation. (order)

If `bind_assoc` does not land in three genuinely different attempts,
dispatch a bounded `grind` loop on it with the verify command `lake build
Graded.Monad`; the shape of the proof is a `cases x` then `simp [cast,
widen_widen, widen_irrel]`, but the exact rewrite set is not known
upfront.

### Consumer

Replace the `-- REPLACED-BY: bind` composition in
`Examples/Validation.lean` with `bind (parseNat s) checkRange`, and the
three-stage version with nested `bind`. The `#eval`s must produce the
same values as before (compare with `#guard`).

### Tests

`Tests/Monad.lean`: each law at `E`; `bind_assoc` instantiated at three
*distinct* concrete grades so `cast` is not `cast rfl`.

### Living doc

`docs/design.md#monad`: the signatures, the five theorems, the
property-per-law list, the `cast` direction decision, and an honest
one-line verdict on the provisional `cast` decision ("casts were
tolerable / dominated" — the integration review reads this).

### Letter

`blog/letters/monad-laws.org`, title "The monad laws are true up to
something, and Lean wants to know up to what". The "Back in C++" section
is important: the C++ instance's `and_then` never had to say `bot_join`;
it relied on `error_set<>` canonicalizing away. That is the same fact
expressed as a type identity instead of a theorem — say so, and say which
you would rather debug.

## Declared file scope

`Graded.lean`, `Graded/Monad.lean`, `Tests.lean`, `Tests/Monad.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#monad`, and the verdict
line under `#carrier`), `blog/letters/monad-laws.org`.

## Spot checks

```
grep -c "REPLACED-BY" Examples/Validation.lean    # 0
grep -n "join_assoc\|bot_join\|join_bot\|join_mono" Graded/Monad.lean
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-monad-laws -b step/monad-laws integration/lean-model
cd ../wt-monad-laws
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-monad-laws.md`
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
monad-laws: pure/bind with union grades; laws stated through cast

The three monad laws hold only up to grade equalities the C++ side
gets from type canonicalization. Stating them through cast records
exactly which pomonoid property each law consumes, and the verdict on
whether cast-based statement is tolerable feeds the provisional
decision in the living doc.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/monad-laws -m "merge step/monad-laws [monad-laws]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-monad-laws
printf '%s\n' '{"step":"monad-laws","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/monad-laws | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-monad-laws
git branch -d step/monad-laws
```

## Handoff

Mark `monad-laws` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-applicative-from-monad.md`. Write `tmp/plan/handoff-applicative-from-monad.md` fresh, per
the contract in `AGENT-PROMPT.md`.
