# step: applicative-from-monad

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

The C++ design states that the applicative instance for a monad *is* the
monad instance (`docs/design.md#cpp-counterpart`). In an ordinary monad
that is a theorem (`ap = bind` in the usual way). In a *graded* monad it
is a claim about grades too: `ap : F_g (α → β) → F_h α → F_{g ⊔ h} β`
derived from `bind` sequences the effects, so it puts `g` before `h`.
With a commutative grade nobody can tell; with a non-commutative one the
"identical" claim would be false in the type. This step derives the
applicative from the monad, proves the applicative laws, and records
exactly where `join_comm` is — and is not — needed. Prediction, to be
confirmed or refuted: the four applicative laws need only unit and
associativity; commutativity is needed only to show `ap` and a
"flipped" `ap` agree, which is the C++ "identical" claim.

## What already exists

`docs/design.md#monad` (`pure`, `bind`, laws, cast direction),
`#subsumption`, `#grade`.

## The change

Create `Graded/Applicative.lean`:

```lean
def ap (f : Graded g (α → β)) (x : Graded h α) : Graded (Grade.join g h) β :=
  bind f (fun f' => bind x (fun a => pure (f' a))) |> cast (by ...)
```
(the inner grade is `h ∪ ∅`; one `join_bot` cast). Also
`map2 (k : α → β → γ) : Graded g α → Graded h β → Graded (join g h) γ`,
and `seqRight`/`seqLeft` if they fall out cheaply — otherwise omit and
note it.

Theorems:

- `ap_pure_id : ap (pure id) x = cast _ x` (identity; unit)
- `ap_comp : ap (ap (ap (pure (· ∘ ·)) u) v) w = cast _ (ap u (ap v w))`
  (composition; associative + unit) — the heaviest proof in the plan so
  far; `grind` loop on `lake build Graded.Applicative` if needed
- `ap_pure_pure : ap (pure f) (pure a) = cast _ (pure (f a))`
  (homomorphism; unit)
- `ap_interchange : ap u (pure a) = cast _ (ap (pure (· a)) u)`
  (interchange) — **this one needs `join_comm`** (`g ∪ ∅` vs `∅ ∪ g` are
  both `g` by the unit laws alone, so check: maybe it doesn't). Whatever
  the answer, it is a finding; record it.
- `ap_flip : ap f x = cast (Grade.join_comm g h) (apFlipped f x)` where
  `apFlipped` runs `x` first. Requires `join_comm` by construction.
  On the *value* side, prove `apFlipped f x = ap f x` **only when at most
  one of them is an error**; give a counterexample in `Tests` where both
  are errors and the two differ (which error survives) — that is the
  content of the C++ "identical" claim: identical grade, and identical
  value only under a condition the C++ never states.

### Consumer

`Examples/Validation.lean`: a pair of independent validations
(`parseNat s₁`, `parseNat s₂`) combined with `map2 (· + ·)`, and the
`#guard` showing which error wins when both fail.

### Living doc

`docs/design.md#applicative`: signatures, the law/property table, and
the finding about `ap_flip`.

### Letter

`blog/letters/applicative-from-monad.org`, title "'The applicative is
identical to the monad' — identical in what?". Explain applicative to a
C++ reader as "the thing that lets you combine independent computations
without a nesting order", and what "independent" costs when both fail.

## Declared file scope

`Graded.lean`, `Graded/Applicative.lean`, `Tests.lean`,
`Tests/Applicative.lean`, `Examples/Validation.lean`, `docs/design.md`
(`#applicative`), `blog/letters/applicative-from-monad.org`.

## Spot checks

```
grep -n "join_comm" Graded/Applicative.lean       # exactly where it was needed
grep -n "counterexample\|both err" Tests/Applicative.lean
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-applicative-from-monad -b step/applicative-from-monad integration/lean-model
cd ../wt-applicative-from-monad
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-applicative-from-monad.md`
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
applicative-from-monad: applicative derived from bind; where commutativity is and is not needed

Checks the C++ claim that the applicative instance is identical to the
monad instance. It is, for grades, by join_comm; for values only when at
most one side fails. The counterexample is recorded so the C++ paper
can state the condition.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/applicative-from-monad -m "merge step/applicative-from-monad [applicative-from-monad]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-applicative-from-monad
printf '%s\n' '{"step":"applicative-from-monad","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/applicative-from-monad | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-applicative-from-monad
git branch -d step/applicative-from-monad
```

## Handoff

Mark `applicative-from-monad` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-applicative-accumulation.md`. Write `tmp/plan/handoff-applicative-accumulation.md` fresh, per
the contract in `AGENT-PROMPT.md`.
