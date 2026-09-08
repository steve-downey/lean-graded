# step: baseline-capture

## Project context

A new Lean 4 project modelling the grading design of P3200 / beman.transpose
(C++): grade pomonoid `error_set` (join-semilattice of error types), carrier
`expected<T, error_set<Es...>>`, bare `T` at grade ∅, subsumption by implicit
conversion, monad/applicative/traversable typeclass objects. Integration
branch: `integration/lean-model`. This step runs **in the main checkout**,
not a worktree, because it creates the project and the branch.

## Why

Nothing exists yet. Every later step needs: a building Lean project with
Mathlib available, a rules pack, a living doc with the anchors later steps
will point at, a Makefile that turns "GREEN" into two commands, a timed row
zero in `metrics.jsonl`, and the blog scaffold. This step also writes letter
0 — the only letter not about a proof — because the reader needs to know why
a C++ standards person is doing this in Lean before letter 1 shows them one.

## Setup

```
cd <repo-root>             # empty git repo on `main`, or `git init` one
git checkout -b integration/lean-model
```

### Fix the metrics path first

Every step file carries the literal placeholder `/home/sdowney/src/lean-graded` for the
absolute path of this checkout. Replace it now, once, in every plan file:

```
ROOT="$(pwd)"
sed -i "s#/home/sdowney/src/lean-graded#${ROOT}#g" tmp/plan/*.md
grep -L "${ROOT}" tmp/plan/step-*.md     # must print nothing
```

## Verify GREEN baseline

There is no baseline; the first green build is the deliverable.

## The change

### 1. Create the Lean project with Mathlib

Use the current Mathlib-recommended bootstrap (a `math` template):

```
lake +leanprover-community/mathlib4:lean-toolchain new transpose_lean math
```

Move the generated contents up into the repo root (or run the command in a
temp dir and copy). Then:

```
lake exe cache get      # Mathlib oleans; if this fails for network reasons, that is a block, not a wait
lake build
```

Rename the library to `Graded` in `lakefile.lean` (`lean_lib Graded`) with
root file `Graded.lean`, plus a second library `Tests` with root `Tests.lean`,
and an `Examples` library with root `Examples.lean`. The exact lakefile
syntax depends on the Lake version the template generates; keep whatever
syntax the template used and add the two libraries in the same style.

Do not hand-pick a Lean version. Take the toolchain the Mathlib template
pins. Record the resulting `lean-toolchain` contents and the Mathlib commit
from `lake-manifest.json` in `docs/design.md#toolchain`.

### 2. `Graded.lean`, `Tests.lean`, `Examples.lean`

Each a root that imports its submodules. Initially:

```lean
-- Graded.lean
import Graded.Prelude
```
```lean
-- Graded/Prelude.lean
/-! Shared imports and the `Graded` namespace. Later steps add modules
    here and to `Graded.lean`. -/
import Mathlib.Data.Finset.Basic
namespace Graded
end Graded
```
`Tests.lean` and `Examples.lean` start as `-- populated by later steps` plus
one trivial `example : True := trivial` each so they build.

### 3. `Makefile`

```make
.PHONY: verify nosorry letters all
all: verify nosorry letters
verify:
	lake build 2>&1 | tee build.log | tail -n 20
	@grep -q "error" build.log && exit 1 || true
nosorry:
	@! grep -rnE "\bsorry\b|\badmit\b|native_decide" Graded Tests Examples --include=*.lean
	@! grep -rnE "^\s*axiom\b" Graded Tests Examples --include=*.lean
letters:
	@scripts/check-letters.sh
```
Note the recipe lines must be tab-indented. `verify` must exit non-zero on
any Lean error; confirm by inserting a deliberate `example : False := by
simp` and watching it fail, then remove it.

### 4. `scripts/check-letters.sh`

For every `- [x] N. [slug]` line in `tmp/plan/checklist.md`, require
`blog/letters/<slug>.org` to exist and to contain the four headings
`* What I set out to do`, `* What the checker refused`, `* What changed`,
`* Back in C++`. `baseline-capture` is exempt from the "refused" heading
(it has none). Exit 1 on the first miss, naming it. `blog-series-edit` is
exempt entirely (its output is the index, not a letter).

### 5. `docs/RULES.md` — the rules pack

Write it with exactly these sections.

**Lean style.** One module per plan step under `Graded/`. `namespace Graded`
throughout. Theorems are `theorem`, not `lemma`. Names are snake_case in
Mathlib style: `join_idem`, `widen_widen`, `bind_pure_left`. Every theorem
that depends on a pomonoid property states it by *citing the named lemma*
from `Graded.Grade` in its proof — never by re-proving it inline with
`Finset` facts — so [oracle-export] can grep which laws need which
properties. Universe-polymorphic `Type u` for carriers unless the step says
otherwise. No `sorry` survives a commit. No `native_decide`. No new
`axiom`.

**Hypothesis discipline.** A theorem takes the *weakest* hypothesis that
proves it, and the step file says what that is expected to be. If the
proof needs more than the step allowed, that is a finding, not a licence:
halt with an amendment (the design may be wrong) rather than strengthening
the hypothesis silently.

**Tests.** `Tests/<Module>.lean` holds `example`s that instantiate every
theorem of the step at a concrete `Err` (use `inductive E | parse | range |
io deriving DecidableEq, Repr` unless the step says otherwise) and at least
one `#guard` or `decide` that *computes*, so the definitions are known to
reduce and not just typecheck.

**Living doc.** `docs/design.md` is updated in place, by anchor. A step
adds or revises the section its step file names; it never appends a log.
Provisional decisions are marked `> **Provisional.** Needed because … .
Revisit when … .` at the anchor.

**Letter template** (`#letter-template`). File `blog/letters/<slug>.org`.
Org header: `#+TITLE: Letter <n>: <title>`, `#+DATE:` today,
`#+CATEGORY: lean-transpose`, `#+STEP: <slug>`. Addressed to a named
correspondent — a working C++ programmer who has never opened Lean; the
addressee name is fixed in `docs/design.md#blog-series` (provisional:
"Dear colleague"). Four headings, in order: `* What I set out to do`,
`* What the checker refused`, `* What changed`, `* Back in C++`. 600–1000
words. Every Lean snippet ≤ 15 lines and immediately explained line by line
in prose; no tactic name appears without saying what it does in plain
words; no category-theory term appears without the C++ thing it names.
Written in first person, past tense, honest about dead ends. No
measurements, no token talk, no mention of agents or plans. The reader is
the person the series is for, not the orchestrator.

### 6. `docs/design.md` — the living doc

Create with these anchors (`##` headings; later steps fill them):

```
# Design — Lean model of graded Transpose
## toolchain            (this step: versions, cache command, build times)
## cpp-counterpart      (this step: the C++ facts below, verbatim)
## grade                ([grade-pomonoid])
## carrier              ([graded-carrier])
## subsumption          ([subsumption-widen])
## monad                ([monad-laws])
## applicative          ([applicative-from-monad], [applicative-accumulation])
## traverse             ([traverse-list], [traverse-tuple])
## compose              ([compose-flatten])
## morphisms            ([graded-morphism])
## representation       ([canonical-representation])
## laws-inventory       ([oracle-export])
## blog-series          (this step: addressee, order, index location)
## provisional-decisions (index of every "Provisional." mark, by anchor)
```

Under `## cpp-counterpart` write exactly these facts (they are the contract
with the C++ side; later steps read them by anchor):

- The grade is `error_set<Es...>`: a set of error *types*, ordered by
  inclusion, joined by union; ∅ is the unit. It is a nominal type, not a
  bare pack. Canonicalization is *type-level identity*:
  `error_set<A,B>` and `error_set<B,A>` are the same type, via a public
  alias delegating to a sorted detail carrier. An instance holds **one**
  error value, whose type is in the set; value equality is variant-style.
- The carrier at grade `Es` is `expected<T, error_set<Es...>>`; at grade ∅
  it is **bare `T`** (decided for client-API risk reasons), so ∅-grade is a
  different C++ type from `expected<T, error_set<>>`.
- Subsumption `Es ⊆ Es'` is an implicit conversion of the carrier.
- `bind` produces the *union* grade; `pure` produces grade ∅.
- The applicative typeclass instance for a monad is stated to be identical
  to (not merely derivable from) the monad instance.
- `traverse` is shape-preserving over ranges and over tuples.
- Typeclass instances are duck-typed "gadgets" needing only a couple of
  functions; no law checking exists in the C++ machinery; std types are the
  intended test probes if a law harness is added.
- Only `error_set` is intended as a grade for now; the design should not
  make it the *only possible* grade.

Under `## blog-series`: addressee (provisional "Dear colleague"), the
letters directory, and that ordering/index is [blog-series-edit]'s job.

### 7. Letter 0

`blog/letters/baseline-capture.org`. Title "Why I'm writing to you from
Lean". Sections per template (the "refused" section may be one paragraph
saying nothing was refused yet and what the reader should expect that
section to contain in later letters). Content: what P3200's grading is in
one paragraph a C++ reader recognizes; that the C++ type system tracks the
grade but checks no law; that the plan is to write the same design a second
time in a language where the laws are theorems, so we learn which
*properties of the grade* each law actually needs; what Lean is, in two
sentences, for someone who has never seen it (a programming language whose
type checker can check proofs; `lake` is its CMake); what `lake exe cache
get` did and how long the first build took (the one measurement allowed in
a letter, because the reader will try this).

### 8. CI

`.github/workflows/ci.yml`: checkout, install elan, `lake exe cache get`,
`make all`. Keep it minimal; if the runner cannot fetch the cache, note it
in the handoff rather than fighting it.

## Verify GREEN after

```
make verify > /dev/null; echo verify=$?
make nosorry; echo nosorry=$?
make letters; echo letters=$?
```
All three zero. Time `make verify` from cold (`rm -rf .lake/build`, cache
still present) and warm; both go in `docs/design.md#toolchain` and in the
row-zero note.

## Spot checks

```
grep -n "lean_lib" lakefile.lean            # Graded, Tests, Examples
grep -c "^## " docs/design.md               # 14
grep -n "Provisional" docs/design.md        # at least blog-series addressee
test -f blog/letters/baseline-capture.org
```

## Commit

```
git add -A
git commit -F- << 'MSG'
baseline-capture: Lean project, rules pack, living doc, letter 0

Establishes the project every later step builds on. The rules pack fixes
theorem naming and the hypothesis discipline now, because the whole point
of the model is knowing which pomonoid property each law needs, and that
is only recoverable if every proof cites the property by name from the
start. The living doc's anchors are created empty so later steps update
in place rather than growing a narrative.
MSG
```
No merge: this step runs on the integration branch directly. Tag the base:
`git tag plan-base`.

## Record measurements

Append **two** rows (row zero = the measured verify floor; row one = this
step) to `/home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl`:

```
printf '%s\n' '{"step":"verify-floor","lane":null,"outcome":"green","wall_seconds":<cold+warm>,"attempts":1,"verify":{"command":"make verify","exit_code":0,"wall_seconds":<warm>,"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":{"files_changed":0,"insertions":0,"deletions":0},"out_of_scope":[],"note":"cold=<s>s warm=<s>s after lake exe cache get"}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
printf '%s\n' '{"step":"baseline-capture","lane":null,"outcome":"green","wall_seconds":<n>,"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":<n>,"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat plan-base~1 | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
(Substitute real numbers; if `git diff --shortstat` against an empty repo
misbehaves, use `git show --shortstat HEAD` instead.)

## Declared file scope

`lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, `Graded.lean`,
`Graded/Prelude.lean`, `Tests.lean`, `Examples.lean`, `Makefile`,
`scripts/check-letters.sh`, `docs/RULES.md`, `docs/design.md`,
`docs/allowed-axioms.md` (empty list), `blog/letters/baseline-capture.org`,
`.github/workflows/ci.yml`, `.gitignore`, `tmp/plan/*.md` (placeholder
substitution only).

## Cleanup

None (no worktree).

## Handoff

Mark this step in `tmp/plan/checklist.md`. Read
`tmp/plan/step-grade-pomonoid.md`. Write `tmp/plan/handoff-grade-pomonoid.md`
per the contract in `AGENT-PROMPT.md`. Things it will need that only you
know: the exact Mathlib import that gave you `Finset` and `Finset.union`
lemmas without a slow import (`Mathlib.Data.Finset.Basic` vs
`Mathlib.Data.Finset.Lattice`), the warm verify time, and any Lake syntax
surprise.
