# RULES — Lean model of graded Transpose

This is the rules pack. It does not change between steps, except to
record an amendment when a step reverses an earlier decision — see
[Amendments](#amendments).

## Lean style

One module per plan step under `Graded/`. `namespace Graded` throughout.
Theorems are `theorem`, not `lemma`. Names are snake_case in Mathlib style:
`join_idem`, `widen_widen`, `bind_pure_left`. Every theorem that depends on a
pomonoid property states it by *citing the named lemma* from `Graded.Grade`
in its proof — never by re-proving it inline with `Finset` facts — so
[oracle-export](../tmp/plan/step-oracle-export.md) can grep which laws need
which properties. Universe-polymorphic `Type u` for carriers unless the step
says otherwise. No `sorry` survives a commit. No `native_decide`. No new
`axiom`.

## Hypothesis discipline

A theorem takes the *weakest* hypothesis that proves it, and the step file
says what that is expected to be. If the proof needs more than the step
allowed, that is a finding, not a licence: halt with an amendment (the
design may be wrong) rather than strengthening the hypothesis silently.

## Amendments

<a id="amendments"></a>

This file does not change between steps. It changes when a step reverses
something a previous step decided, and then it records what was reversed
and why, so the reversal is visible to a reader who only has this file.

### Carrier universes: the tag-only payload is pinned — 2026-09-10

The style rule says "universe-polymorphic `Type u` for carriers unless
the step says otherwise". [payload-carrier] needs an exception stated
rather than discovered.

`ErrorSignature` carries two universes: `Kind : Type u` and
`Payload : Kind → Type v`. `ExpectedG` over such a signature, at payload
type `α : Type w`, lives in `Type (max u v w)`. `Graded` is the
specialization at `tagOnly Err`, and its result universe can only be
stated as `Type (max u v)` — the universe it has always had — if the
signature's payload universe is known to be no larger. Left free it is an
unsolvable constraint, and Lean reports it as "stuck at solving universe
constraint" at the specialization rather than at `tagOnly`.

So `tagOnly` is pinned: `ErrorSignature.{u, 0}`, payload `Unit` rather
than a polymorphic `PUnit`. This costs nothing — a tag carries no data,
so there is nothing to be polymorphic about — and it applies **only** to
the tag-only signature. A real signature keeps a free payload universe,
and `Examples/Payload.lean` is one.

The general rule stands for carriers. This records that the *signature*
of the tag-only specialization is the one place a universe is fixed, and
why.

### Class mixins are parameterised, not `extends` — 2026-09-10

[obligation-layering] decided that a mixin over `Graded.PreorderedGradeMonoid`
(then `Pomonoid`) should `extends` it, so that instance search had exactly
one route to the base class and no two `Pomonoid G` terms could disagree.
[grade-join-strength] reverses that: mixins take the base class as an
instance **parameter** (`class IsIdemGrade (G) [PreorderedGradeMonoid G] :
Prop`), and carry no data of their own.

The reason is that the `extends` form cannot express the separation the
model now needs. `Pack Err` (`List Err` under `++`) inhabits `IsLubGrade`
and refutes `IsPartialOrderGrade`; `Grade Err` inhabits both; `Nat`
inhabits the second and not the first. Under `extends`, asking for two
mixins at once means two independent copies of the base class, which is
the diamond the original decision existed to prevent. Under the
parameterised form the base instance is *indexed*, not carried, so there
is exactly one such term by construction rather than by discipline, and
`[IsCommGrade G] [IsIdemGrade G]` is a well-formed conjunction — which is
why `IsCanonicalGrade` could stop being a class with duplicated fields and
become an `abbrev` for that conjunction.

This changes the *spelling* of a hypothesis, never its strength: a theorem
that took `[IsIdemGrade G]` alone now takes `[PreorderedGradeMonoid G]
[IsIdemGrade G]`, which is the same requirement written with the base
instance named instead of projected out. No operational theorem in
`Graded/` is affected — none of them mentions these classes at all.

## Tests

`Tests/<Module>.lean` holds `example`s that instantiate every theorem of the
step at a concrete `Err` (use `inductive E | parse | range | io deriving
DecidableEq, Repr` unless the step says otherwise) and at least one `#guard`
or `decide` that *computes*, so the definitions are known to reduce and not
just typecheck.

**This is enforced, not reviewed.** `make test-coverage` classifies every
theorem and applies one rule per class:

| class | detection | rule |
|---|---|---|
| counterexample | conclusion is a `¬` or `≠` | a test names it |
| reduction | proof is `rfl` | its module's test file has a computing `#guard`/`decide` |
| law | everything else | a test names it |

"Names it" is checked against comment-stripped source and against the name
*as declared*, dot-qualification included: prose mentioning a theorem does
not count, an import does not count, and a theorem whose last name segment
happens to match another theorem's does not count for that other one.

Exemptions live in `scripts/coverage-exemptions.json`, an object mapping a
theorem name to the reason it is exempt. Every entry is reviewed, and the
file is meant to stay near-empty — it was introduced at
[coverage-enforcement] with **zero** entries, and an entry is a finding
about the theorem, not a way to quiet the check.

**Fixtures are the labour, and they are the point.** A test that
instantiates a theorem at a degenerate fixture passes the check above and
proves nothing. So:

- associativity and other cast-bearing laws use **three distinct nonempty
  grades**, so the transport is real;
- commutativity tests use **distinct nonempty grades on both sides**;
- heterogeneous tuple tests carry at least **two distinct payload types
  and two distinct grades**;
- morphism cast tests use a **nontrivial grade equality**, never `g = g`,
  and a **many-to-one** renaming, never the identity;
- both-error tests use **distinguishable kinds**, so which error survived
  is visible;
- accumulating traversal tests include **zero, one, and several**
  failures.

None of that is mechanically checkable, which is exactly why it is written
down here rather than left to the script.

## C++ obligations

A law with a consequence for the C++ implementation earns a `CPP_LAW`
entry in `scripts/laws-inventory.py` **in the same change that proves
it**. That column is the sync channel: `docs/probe-harness.md` is
generated from the non-`—` rows, and it is what the C++ side reads.

A finding that never reaches the column has not been communicated,
however well it is written up in `docs/design.md`. Tranches C through G
proved five modules' worth of results with C++ consequences and added
zero equations, so the harness went on describing the model as it stood
before them — see [cpp-sync](design.md#cpp-sync).

Two cautions. The table is keyed by **bare theorem name**, so a name
declared in two modules with different C++ meanings must not get an entry
at all (`apK_comp` is the live example). And a result about the model's
own internals is not an obligation: the test is whether a C++
implementation could be *checked* against it.

## Axioms

`make nosorry` is a text grep: it cannot see an axiom reached through a
dependency, nor a `sorry` in a declaration nothing references. `make
axioms` runs `#print axioms` over every `law`-class declaration and asserts
the transitive closure is a subset of `{propext, Classical.choice,
Quot.sound}` — Lean's own three. Keep both; neither subsumes the other.

## Living doc

`docs/design.md` is updated in place, by anchor. A step adds or revises the
section its step file names; it never appends a log. Provisional decisions
are marked `> **Provisional.** Needed because … . Revisit when … .` at the
anchor.

## Letter template

<a id="letter-template"></a>

File `blog/letters/<slug>.org`. Org header: `#+TITLE: Letter <n>: <title>`,
`#+DATE:` today, `#+CATEGORY: lean-transpose`, `#+STEP: <slug>`. Addressed to
a named correspondent — a working C++ programmer who has never opened Lean;
the addressee name is fixed in `docs/design.md#blog-series` (provisional:
"Dear colleague"). Four headings, in order: `* What I set out to do`,
`* What the checker refused`, `* What changed`, `* Back in C++`. 600–1000
words. Every Lean snippet ≤ 15 lines and immediately explained line by line
in prose; no tactic name appears without saying what it does in plain
words; no category-theory term appears without the C++ thing it names.
Written in first person, past tense, honest about dead ends. No
measurements, no token talk, no mention of agents or plans. The reader is
the person the series is for, not the orchestrator.
