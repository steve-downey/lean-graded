# RULES — Lean model of graded Transpose

This is the rules pack. It does not change between steps.

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

## Tests

`Tests/<Module>.lean` holds `example`s that instantiate every theorem of the
step at a concrete `Err` (use `inductive E | parse | range | io deriving
DecidableEq, Repr` unless the step says otherwise) and at least one `#guard`
or `decide` that *computes*, so the definitions are known to reduce and not
just typecheck.

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
