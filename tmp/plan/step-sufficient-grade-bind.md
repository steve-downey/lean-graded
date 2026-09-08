# step: sufficient-grade-bind

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

Added 2026-09-08 after the integration review, which found the cast
burden had outgrown [monad-laws]'s "tolerable, not dominating" verdict.

## Why

Measured, not asserted: **39 of the model's 146 theorems carry a `cast` in
their statement** (26%), and in `Graded/Monad.lean` it is 7 of 8. The
review's specific complaints are real: `Comp.ap_interchange` carries six
casts in one statement, `GradedHom` has cast-quantified *fields*, and
`Graded/Ungraded.lean` is 0 of 16 — at one fixed grade the casts vanish
entirely, which is what makes the burden visibly a *grade-arithmetic* cost
rather than an unavoidable one.

`docs/design.md#carrier` recorded the alternative from the start: `bind` at
any sufficient grade `k` with `g ∪ h ⊆ k`, "which would remove every
`cast`". [monad-laws] judged the casts tolerable and no amendment followed.
The review's verdict is that this was right for one grade coordinate at
step 5 and does not describe a two-coordinate composite.

**But the naive reading of that alternative is a trap, and this step exists
partly to avoid it.** The casts are not noise. They record, faithfully,
that the C++ `bind` *computes the union grade*
(`docs/design.md#cpp-counterpart`) and that the monad laws therefore hold
only up to grade equalities the C++ gets from canonicalization. Replacing
the union-graded `bind` with a sufficient-grade one would remove the casts
by modelling a **different design** — one where the caller nominates the
result grade. That is a real alternative worth knowing about, but it is not
P3200, and a model that quietly became prettier by becoming unfaithful
would be worse than the casts.

So the shape is not replacement. It is **two layers and a bridge**, and the
orchestrator has already established that this works (see below): the
union-graded `bind` stays exactly as it is, the sufficient-grade `bindK` is
added beside it, and one theorem says they are the same operation. Then the
C++-faithful statement is still the one the paper describes, and reasoning
that does not care about the exact grade can be done cast-free.

## What already exists

`docs/design.md#monad` (`bind`, `pure`, the five laws, the cast direction
convention), `#subsumption` (`widen`, `widen_irrel`, `fromEmpty`),
`#carrier` (`cast`, `cast_ok`/`cast_err`/`cast_widen` — note these live in
`Graded/Monad.lean`, not `Carrier.lean`), `#grade`.

## Established before this step — do not re-derive, do check

The orchestrator spiked this. Three facts, each verified by building them;
reproduce them rather than inventing your own shape.

```lean
def bindK (hg : g ⊆ k) (hh : h ⊆ k) (x : Graded g α) (f : α → Graded h β) :
    Graded k β :=
  match x with
  | .ok a     => widen hh (f a)
  | .err e he => .err e (hg he)
```

1. **The laws state cast-free.** All three elaborate with no `cast`
   anywhere: `bindK (Grade.bot_le k) hh (pure a) f = widen hh (f a)`;
   `bindK hg (Grade.bot_le k) x pure = widen hg x`; and associativity with
   every grade the same `k`, so there is nothing to re-associate at the
   type level at all. The first is `rfl`; the second is a two-case split.
2. **Associativity needs reduction lemmas, exactly as every earlier step
   found.** With `bindK_ok`/`bindK_err` in hand the outer cases go through;
   the spike's remaining leaf was a `widen` application sitting where a
   constructor was needed, which is the "reduction lemmas first" pattern
   the handoffs have recommended since [applicative-from-monad]. Write
   `bindK_ok`, `bindK_err`, and reduction lemmas for `widen` on each
   constructor if `Graded/Widen.lean` does not already have them, and do
   **not** reach for `change`/manual unfolding first.
3. **The bridge is `rfl`.** `bind x f = bindK (Grade.le_join_left g h)
   (Grade.le_join_right g h) x f` closes by `rfl` in both constructor
   cases. This is the theorem that makes the two layers coexist.

## The change

Create `Graded/Sufficient.lean` (import in `Graded.lean`).

- `bindK` as above, plus `pureK : α → Graded k α := fromEmpty` (reuse it,
  do not redefine), plus the reduction lemmas.
- `bindK_pure_left`, `bindK_pure_right`, `bindK_assoc` — **cast-free
  statements, and that is the deliverable.** Report which pomonoid
  properties each consumed; expect the *order* lemmas to do the work the
  unit and associativity lemmas used to do, since the grade arithmetic has
  become subsumption.
- `bindK_widen`: the analogue of `bind_widen`. Expect it to be cheaper.
- `bind_eq_bindK`, the bridge. Tag it `/-- BRIDGE -/` so
  [oracle-export]'s script can be taught to recognise the pair later.
- `bindK_irrel`: which proof of `g ⊆ k` was used does not matter, by proof
  irrelevance, mirroring `widen_irrel`. State it; it is what makes the
  threaded `⊆` arguments free at call sites, and if it is *not* free that
  is the finding that sinks this design.

### The measurement, which is this step's real output

A short table in the living doc comparing, for the three monad laws only:
casts in the statement (before / after), lines of proof (before / after),
and what a call site pays (the union version threads nothing; the
sufficient version threads two `⊆` proofs). Then a one-line verdict:
whether the cast-free layer is worth extending to the applicative and
traversal layers. **A verdict of "not worth it" is a perfectly good outcome
and closes the question** — say so plainly if the threaded proofs cost more
at call sites than the casts cost in statements.

### Consumer

`Examples/Validation.lean`: add `validateK`, the same two-stage validation
through `bindK` at the literal grade `{E.parse, E.range}`, with a `#guard`
showing it renders identically to `validate`. Leave `validate` alone — the
point is that both spellings exist and agree.

### Tests

`Tests/Sufficient.lean`: each law at `E`; a `#guard` that computes; and one
`example` instantiating `bindK` at a `k` strictly larger than the join, so
the "sufficient, not exact" case is exercised and not just the bridge case.

### Living doc

`docs/design.md#monad`: a `### The sufficient-grade layer` subsection — the
definition, the cast-free laws, the bridge theorem, the measurement table,
the verdict. Then update `#carrier`'s provisional block with the verdict,
in place, since that is where the alternative was first recorded. Do not
add a new top-level anchor.

### Letter — this one is the point, not a by-product

`blog/letters/sufficient-grade-bind.org`, **Letter 17**, title "The casts
were telling me something, and it wasn't 'clean me up'". The series' own
closing letter is Letter 16; this one comes after it, which the letter
should acknowledge in its first line rather than pretend otherwise.

It has to do three things for a C++ reader who has never opened Lean:

1. **Explain the difficulty honestly.** Why a cast appeared at all: `bind`
   returns the union grade, so `(g ∪ h) ∪ j` and `g ∪ (h ∪ j)` are the same
   set but not the same *expression*, and Lean will not let you write one
   where the other is expected without saying why. In C++ the two spell the
   same type after canonicalization and nobody notices. Give one law's
   statement in both forms and let the reader see the noise.
2. **Explain why the obvious fix is wrong.** Letting the caller nominate a
   sufficient grade removes every cast and models a design P3200 does not
   have. Name that trap plainly; it is the most useful paragraph in the
   letter, and the honest reason the casts survived twelve steps.
3. **Explain the actual fix.** Two layers and a one-line bridge: the
   faithful union version for describing C++, the sufficient-grade version
   for reasoning, and a theorem saying they are the same operation. Then
   whichever the measurement says, say it — including "and it turned out
   not to be worth extending".

Also update `blog/letters/index.org` to add this letter after the closing
one, with a one-line note that the series continued past its own ending.
Do not renumber the existing letters.

## Declared file scope

`Graded.lean`, `Graded/Sufficient.lean`, `Tests.lean`,
`Tests/Sufficient.lean`, `Examples/Validation.lean`, `docs/design.md`
(`#monad` and `#carrier`'s provisional block only),
`blog/letters/sufficient-grade-bind.org`, `blog/letters/index.org`.

**No existing theorem's statement may change, and `Graded/Monad.lean` must
not be edited.** The whole design of this step is that the union layer
stays untouched. If you find you must change it, that is
`amendment-sufficient-grade-bind.md` and a halt.

## Spot checks

```
git diff --name-only integration/lean-model~1...HEAD -- Graded/ | grep -v Sufficient   # empty
grep -c "cast" Graded/Sufficient.lean          # low: the bridge mentions none
grep -n "BRIDGE" Graded/Sufficient.lean
grep -n "def bind\b" Graded/Sufficient.lean    # nothing: no second union bind
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-sufficient-grade-bind -b step/sufficient-grade-bind integration/lean-model
cd ../wt-sufficient-grade-bind
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true
START=$(date +%s)
```

## Verify GREEN baseline

```
make all > /dev/null; echo all=$?      # must be 0
```
If non-zero before you change anything, stop: `blocked-sufficient-grade-bind.md`.

## Verify GREEN after

```
make verify > /dev/null; echo verify=$?
make nosorry; echo nosorry=$?
make letters; echo letters=$?
make laws; echo laws=$?
```
All zero. `make laws` will fail until you regenerate `docs/laws.md` — this
step adds theorems, so run `python3 scripts/laws-inventory.py` and commit
the regenerated table. Read `tail -n 20 build.log` only.

## Commit and merge back

```
git add -A
git commit -F- << 'MSG'
sufficient-grade-bind: the cast-free layer, the union layer, and one theorem between them

The casts record that C++ bind computes the union grade and the laws hold
only up to grade equalities. Removing them by letting the caller nominate
the grade would model a different design. So both layers exist: the union
one describes C++, the sufficient-grade one is cast-free to reason in, and
bind_eq_bindK says they are the same operation. The measurement decides
whether the applicative and traversal layers follow.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/sufficient-grade-bind -m "merge step/sufficient-grade-bind [sufficient-grade-bind]"
```

Stage files **by name** in the main checkout; not `git add -A` there.

## Record measurements

```
END=$(date +%s)
cd ../wt-sufficient-grade-bind
printf '%s\n' '{"step":"sufficient-grade-bind","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"verify_runs":<n>,"edit_iterations":<n>,"proof_attempts":<n>,"verify":{"command":"make verify","exit_code":0,"log_bytes":'"$(wc -c < build.log)"'},"diff":'"$(git diff --shortstat integration/lean-model~1...step/sufficient-grade-bind | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Note the schema change: the integration review found `attempts` conflated
three quantities and never measured the stop rule. Use `verify_runs` (full
`make verify` runs intending GREEN), `edit_iterations` (cheap targeted
`lake build` calls), and `proof_attempts` (genuinely different approaches
to a single theorem — the number the halt rule is about).

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-sufficient-grade-bind
git branch -d step/sufficient-grade-bind
```

## Handoff

Mark `sufficient-grade-bind` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-sufficient-grade-applicative.md`. Write
`tmp/plan/handoff-sufficient-grade-applicative.md` fresh, per the contract
in `AGENT-PROMPT.md`. **State your verdict in it explicitly**, because that
step is gated on it: if the measurement says the cast-free layer is not
worth extending, the next step does not run and the handoff should say so
in its first line.
