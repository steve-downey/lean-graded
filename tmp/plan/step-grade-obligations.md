# step: grade-obligations

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

Added 2026-09-08, after the original plan, together with
[ungraded-baseline].

## Why

`docs/design.md#cpp-counterpart` ends with a requirement nothing in this
model has tested: *"Only `error_set` is intended as a grade for now; the
design should not make it the only possible grade."* Thirteen steps have
each recorded which pomonoid property a law consumes, but `Grade Err` is
a concrete `abbrev` for `Finset Err`, so nothing has ever *forced* a
proof to use only the recorded properties, and no second grade has ever
been tried. The accumulated table is a set of observations, not an
obligation.

This step turns it into one, and the shape of the answer is the finding:
**the obligations are layered, and which layer you need depends on which
laws you want.**

- A **pomonoid** — associative join, unit, partial order, monotone join —
  carries the monad laws, the applicative laws, subsumption and
  morphisms. Everything through [graded-morphism].
- **Commutativity** on top of that buys `ap_flip` ([applicative-from-monad])
  and tuple order-independence `joinAll_perm` ([traverse-tuple]) — which
  is what licenses `error_set<A,B>` ≡ `error_set<B,A>`.
- **Idempotence** on top of that buys length-independence of the
  traversal grade `foldGrade_cons_ne_nil` ([traverse-list]) and `joinAll_dedup`
  — which is what makes the C++ `traverse` signature writable at all.

That layering is the paper's answer to "what must a grade be", and it is
sharper than "a join-semilattice with a bottom", because it says which
half of the design you lose if you drop each axiom.

The demonstration is a second grade that is deliberately **not**
idempotent: the naturals under `+`, with `0` and `≤`. A perfectly good
commutative pomonoid. At that grade the traversal grade *grows with the
list*, so the C++ signature would not be writable — turning
[traverse-list]'s idempotence finding from a claim into something a
reader can run.

## What already exists

`docs/design.md#grade` (the named property lemmas), `#traverse`
(`foldGrade`, `foldGrade_le`, `foldGrade_cons_ne_nil`, `joinAll`,
`joinAll_perm`, `joinAll_dedup`), and the per-law property records at
every other anchor.

## Scope: this step adds, it does not refactor

**Do not generalize the carrier.** `Graded g α` stays exactly as it is,
indexed by `Finset Err`. Rewriting the model to be generic over an
abstract grade would touch every module and change every existing
theorem's statement, which is an "ask" at best and a rewrite at worst,
and it is not what this step is for.

What makes this tractable is that **the grade algebra is separable from
the carrier**: `foldGrade` and `joinAll` are functions on grades alone
and never mention `Graded`. Those can be stated generically over an
abstract grade with no carrier involved, which is where the whole
demonstration lives. The carrier-level laws are connected to the layers
by *documentation citing their existing recorded properties*, not by
re-proving them abstractly.

If you find you cannot state the obligations without touching the
carrier, that is a real finding about how the model is factored: halt
with `tmp/plan/amendment-grade-obligations.md` saying so. Do not begin a
refactor.

## The change

Create `Graded/Obligations.lean`.

### 1. The layered classes

Check Mathlib first for anything that already says this (`SemilatticeSup`,
`OrderedAddCommMonoid`, `CovariantClass` and friends) and record what you
found, but **state the classes fresh** rather than inheriting: the project
deliberately kept `Grade` off Mathlib's lattice classes so that lemma use
stays greppable ([grade-pomonoid], `docs/design.md#grade`), and the same
reasoning applies here. Say in the living doc which Mathlib classes are
close and why they were not used.

Three layers, each a separate class so an instance can satisfy one and
not the next:

```lean
class Pomonoid (G : Type u) where
  join : G -> G -> G
  bot  : G
  le   : G -> G -> Prop
  -- assoc, bot_join, join_bot, le_refl, le_trans, bot_le,
  -- le_join_left, le_join_right, join_le, join_mono

class IsCommPomonoid (G : Type u) extends Pomonoid G where
  join_comm : forall a b, join a b = join b a

class IsIdemPomonoid (G : Type u) extends IsCommPomonoid G where
  join_idem : forall a, join a a = a
```

Name the fields to match `Graded/Grade.lean`'s existing theorem names
exactly, so `oracle-export`'s grep sees one vocabulary and not two.

Whether idempotence should extend the commutative layer or sit beside it
is a judgment call: `error_set` has both, but they are independent
axioms. Pick one, and **say in the living doc why**, marking it
provisional.

### 2. `Finset Err` satisfies all three

Instances built from the existing named lemmas in `Graded.Grade` —
`join_assoc`, `bot_join`, `join_bot`, `le_join_left`, `le_join_right`,
`join_le`, `join_mono`, `le_refl'`, `le_trans'`, `bot_le`, `join_comm`,
`join_idem`. Cite them; do not reprove them. If a field has no
corresponding existing lemma, that gap is a finding — record it rather
than proving it inline.

### 3. The generic grade algebra

Restate, over an abstract `[Pomonoid G]`, the two grade-level functions
and their theorems:

```lean
def foldG [Pomonoid G] (g : G) : List A -> G      -- bot at [], join g .. at cons
def joinAllG [Pomonoid G] : List G -> G
```

- `foldG_le : foldG g xs <= g` — expect `Pomonoid` alone.
- `foldG_cons_ne_nil : xs <> [] -> foldG g xs = g` — expect
  `IsIdemPomonoid`. **This is the theorem the whole step is about**:
  it should not typecheck at the `Pomonoid` layer.
- `joinAllG_perm : gs ~ gs' -> joinAllG gs = joinAllG gs'` — expect
  `IsCommPomonoid`.

Report what each actually required. If one needs a weaker layer than
expected, that is a better result than confirmation.

### 4. The counter-instance: naturals under `+`

```lean
instance : IsCommPomonoid Nat  -- join = (+), bot = 0, le = (<=)
```
— commutative, ordered, monotone, and **not** idempotent (`1 + 1 <> 1`),
so it must not be given an `IsIdemPomonoid` instance.

Then the demonstration, executable:

- `#guard foldG (1 : Nat) [(), (), ()] = 3` — the traversal grade grows
  with the list. Contrast with `#guard foldG ({E.parse} : Grade E) [(), (), ()] = {E.parse}`.
- `example : ¬ (forall (g : Nat) (xs : List Unit), xs ≠ [] -> foldG g xs = g)`
  — a proof, from the `#guard`'s witness, that `foldG_cons_ne_nil` is
  *false* at this grade. This is the step's headline: the C++ `traverse`
  signature is writable for `error_set` because unions are idempotent,
  and would not be for a counting grade.
- `joinAllG_perm` **does** hold at `Nat` (addition is commutative), so
  order-independence survives while length-independence does not. Show
  both, adjacent — the two axioms buy different things and this is the
  clearest place to see it.

### 5. Optional, only if cheap

A **non-commutative** instance — the free monoid (`List X` under `++`,
`[]`, with `<+:` prefix as the order) — to show `joinAllG_perm` failing
where `foldG_le` still holds. Include it only if it lands quickly; if
not, note in the living doc that the commutative layer's necessity is
argued but not demonstrated, which is an honest weaker claim.

### Consumer

**None.** `Examples/Validation.lean` is not in this step's declared
scope. Do not add one.

### Tests

`Tests/Obligations.lean`: the instances resolve; the `#guard`s above; a
`decide` that computes.

### Living doc

New anchor `## obligations`, after `## ungraded-baseline`. Contents: the
three layers; a table mapping each layer to the laws it buys, citing
each law by the name it has in `Graded/*.lean`; the `Nat` demonstration;
the provisional note on the class hierarchy's shape; and what Mathlib
classes were considered and why they were not inherited from.

### Letter

`blog/letters/grade-obligations.org`, title "What a grade has to be, and
what you lose when it isn't". "Back in C++": P3200 says `error_set` is
not meant to be the only possible grade — here is the interface a grade
must satisfy, in three layers, and here is a perfectly reasonable
alternative grade (count the failures) where `transpose` over a range
would not typecheck, because the grade grows with the range's length.

## Declared file scope

`Graded.lean`, `Graded/Obligations.lean`, `Tests.lean`,
`Tests/Obligations.lean`, `docs/design.md` (`#obligations`),
`blog/letters/grade-obligations.org`.

**No existing `Graded/*.lean` module may change.** That is the point of
the scope section above and is spot-checked below.

## Spot checks

```
git diff --name-only integration/lean-model~1...HEAD -- Graded/ | grep -v Obligations   # must be empty
grep -n "class Pomonoid\|IsCommPomonoid\|IsIdemPomonoid" Graded/Obligations.lean
grep -n "instance.*Nat" Graded/Obligations.lean          # the counter-instance
grep -n "Grade.join_idem\|Grade.join_comm" Graded/Obligations.lean   # instances cite, not reprove
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-grade-obligations -b step/grade-obligations integration/lean-model
cd ../wt-grade-obligations
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-grade-obligations.md`
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
grade-obligations: what a grade must be, in three layers, and a grade that isn't

The design says error_set should not be the only possible grade, and
nothing had tested that. The obligations are layered: a pomonoid carries
the monad, applicative, subsumption and morphism laws; commutativity
adds order-independence; idempotence adds length-independence. The
naturals under + are a commutative pomonoid that is not idempotent, and
at that grade the traversal grade grows with the list — so the C++
traverse signature is writable for error_set because unions are
idempotent, and would not be for a counting grade.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/grade-obligations -m "merge step/grade-obligations [grade-obligations]"
```

Stage your files **by name** for anything committed in the main checkout;
do not use `git add -A` there. See your inbound handoff.

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-grade-obligations
printf '%s\n' '{"step":"grade-obligations","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/grade-obligations | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-grade-obligations
git branch -d step/grade-obligations
```

## Handoff

Mark `grade-obligations` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-oracle-export.md`. Write `tmp/plan/handoff-oracle-export.md` fresh, per
the contract in `AGENT-PROMPT.md`. It needs the layer-to-law table's
exact names and the class field names, since it mechanizes both.
