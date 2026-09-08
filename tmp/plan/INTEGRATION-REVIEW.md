# Integration review — Lean model of graded Transpose

Scoped `model: opus` consult, 2026-09-08, on `integration/lean-model` at
`993ac99`. Boot: `codebase-map.md`, `handoff-integration-review.md`,
`metrics.jsonl`, and the tree at `git diff plan-base..integration/lean-model`
(88 files, +12509/-112, no deletions).

**Verified state.** `make all` re-run cold in this session: exit 0.
`lake build` green (735 jobs), `nosorry: clean`, `check-letters.sh` silent,
`laws-inventory: 146 theorems tabulated, 0 flagged`, `git diff --exit-code`
on the generated docs clean. Working tree clean, no stray worktrees.
Stronger than `make nosorry` (which is a grep): `#print axioms` on nine
headline theorems — `Grade.join_idem`, `bind_assoc`, `ap_flip`,
`traverseComp_eq`, `flatten_ap`, `sumEquiv_bindF`, `joinAll_perm` and kin —
reports `[propext, Classical.choice, Quot.sound]` and nothing else. No
`sorryAx`, no project axiom, anywhere in the closure. `docs/allowed-axioms.md`
is honestly empty.

**The run was genuinely fanned out** — 17 cleared `model: sonnet` workers,
one per step, confirmed by the orchestrator and consistent with every row's
own `note`. `metrics.jsonl` is promoted (§4).

---

## 1. Findings for the C++ side

Read first. Each row names the theorem that establishes it and the letter
that explains it to a C++ reader. "P3200" is the transpose paper;
"the Monad paper" is its companion.

### 1.1 The applicative is identical to the monad — in the type, not in the value

`docs/design.md#cpp-counterpart` records the C++ design's claim that the
applicative typeclass instance for a monad *is* the monad instance. The
model splits that claim in two.

- **Grade: unconditionally identical.** `ap f x` sits at `g ⊔ h`,
  `apFlipped f x` at `h ⊔ g`, and `Grade.join_comm` identifies them. No
  hypothesis.
- **Value: identical only when at most one side errs.**
  `Graded.ap_flip` (`Graded/Applicative.lean:163`) carries
  `(∃ f', f = .ok f') ∨ (∃ a, x = .ok a)` and is false without it —
  `Tests/Applicative.lean:62-80` is the both-errors counterexample.

So a monad-derived `ap` has silently chosen which of two independent
failures the caller sees. **P3200 should say so**: either state a
leftmost-failure-wins contract callers may rely on, or say the choice is
unspecified. Saying nothing is the current state and is the one thing that
cannot be right. **Letter 5.**

And this is *not* a cost of grading. `docs/design.md#ungraded-baseline`
takes the law apart at a fixed grade: the grade-level obstruction
evaporates (`g ⊔ g` against itself), the value-level disagreement survives
completely. It would hold identically for a plain `std::expected`-shaped
applicative. **Letter 13.**

### 1.2 Error accumulation can never be the monad's applicative

`Graded.Accum.notMonad` (`Graded/Accum.lean:235`) is an impossibility
theorem, not an observation: there is **no** `bind` of the graded shape
whose derived `ap` equals `Accum.ap`. The accumulating applicative needs
its own carrier, and that carrier is a genuinely separate inductive type
in the model, not a wrapper.

Consequence for the C++ design: "the applicative instance is identical to
the monad instance" is a sound rule for the short-circuiting applicative
and an *impossible* one the moment error accumulation is wanted. If P3200
or the Monad paper ever offers accumulation, it must be a separate
concept with a separate gadget, and the identity claim must be scoped to
exclude it. **Letter 6.**

The good news, and it is better than expected: `Accum.toGraded_grade'`
(`Graded/Accum.lean:321`) proves the projection from the accumulating
carrier to the single-error one is an applicative morphism
**unconditionally** — `toGraded (ap f x) = Graded.ap (toGraded f) (toGraded x)`
on every input, including both-error. So "collect everything, then throw
all but the first away" is exactly the short-circuiting answer, by
construction. That is a free interoperability guarantee the C++ design can
state.

### 1.3 If P3200 ever states a composition law, it must be about the unflattened pair

`Graded.traverseComp_eq` (`Graded/ComposeApp.lean`) holds
**unconditionally** over `Comp g h α := Graded g (Graded h α)` — two
grades kept separate, no `flatten`, no hypothesis. It is recognisably
Mathlib's `LawfulTraversable.comp_traverse` and it cost only
`Grade.join_idem` per component.

The flattened form is **false**, refuted by an `#eval`-checked
counterexample (`tmp/plan/blocked-compose-flatten.md`), and
`Graded.flatten_ap` (`Graded/ComposeApp.lean:382`) is the mechanism:
`flatten` is an applicative morphism from the composite to the
union-graded carrier only under a three-way condition, and fails outright
without it. `flatten` destroys which layer failed.

Crucially the refutation **is not about grading** — re-run at a fixed
grade in `Tests/Ungraded.lean` it still fails, and it fails identically
for an ungraded `expected<expected<T,E>,E>`. `#cpp-counterpart` currently
makes no composition claim, so nothing breaks today. But the shape of the
claim P3200 may not make is now known. **Letters 9 and 12.**

### 1.4 The grade obligations, and the one question the paper has to answer

`#cpp-counterpart` ends: "Only `error_set` is intended as a grade for now;
the design should not make it the *only possible* grade." The model turns
that into a stated obligation with three layers
(`Graded/Obligations.lean`):

| layer | buys | fails at |
|---|---|---|
| `Pomonoid` (assoc, unit, order, `join_mono`) | `bind`/`ap` laws — `bindF_*`, `apF_*` | — |
| `IsCommPomonoid` | order-independence — `joinAllG_perm`, `joinAll_perm` | — |
| `IsIdemPomonoid` | length-independence *and* boundedness — `foldG_cons_ne_nil`, `foldG_le` | `Nat` under `+`: `nat_not_idem` |

The `Nat` instance is a real witness, not an illustration:
`foldG (1:Nat) [(),(),()] = 3` and `3 ≤ 1` is false.

**The headline correction to the plan's own prediction**: `foldG_le` —
even the *bound*, `foldG g xs ≤ g` — needs `IsIdemPomonoid`, not bare
`Pomonoid`. `error_set` gets boundedness free only because `Finset` union
genuinely is a lattice join. Any other grade pays for it. **Letter 14.**

**And the open question P3200 must decide**, recorded as
`docs/design.md#grade-join-strength` (**OPEN**): must a grade's `join` be
a *least upper bound*, or merely an associative, unital, monotone
operation?

- *Least upper bound.* `join_le` plus antisymmetry **proves** `join_idem`
  (verified in Lean). Idempotence is not an axiom at all, length-
  independence is free for any grade worth the name, the paper's
  obligation is one short strong sentence — and `Nat`-style counting
  grades are simply not grades.
- *Ordered monoid.* Idempotence is a real, separate requirement,
  counting grades are admissible, and `traverse` is **not available**
  for them at all.

This is a judgment about what P3200 wants to promise, not about the code,
and the three-layer story above is a true account of the *weaker* reading
only. **This is the finding to read first.**

### 1.5 The canonicalization mechanism needs a total order on error types, which the design has never named

`Graded/Canonical.lean`'s `Canon Err := { l : List Err // l.SortedLT }`
requires `[LinearOrder Err]`, where `Grade Err := Finset Err` needs only
`[DecidableEq Err]`. `canonEquiv` proves the two spellings are `Equiv`, so
the C++ "public alias delegating to a sorted detail carrier" strategy is
**validated** — `error_set<A,B>` and `error_set<B,A>` really are the same
type, and `joinAll_perm` / `joinAll_dedup` prove permutation- and
duplicate-invariance.

But the model records a finding the C++ design has not: `DecidableEq` is
nominal typing, which C++ gets free; `LinearOrder` is a *total order over
error types*, which C++ does not. Sorting the detail carrier requires
picking one — `std::type_index`'s `<`, a mangled-name comparison, an
explicit enumeration — and each choice has consequences (`type_index`
ordering is unspecified across translation units and across runs).
`#cpp-counterpart` should name the ordering it intends. **Letter 11.**

### 1.6 Subsumption really is a functor, and it is free

`widen_refl`, `widen_widen`, `widen_map`, `widen_cast`, `widen_irrel`
(`Graded/Widen.lean`) and `bind_widen` (`Graded/Monad.lean`) together say:
an implicit widening conversion inserted anywhere in an expression gives
the same answer. `widen_map` and `widen_cast` need **no** pomonoid
property at all, and `widen_irrel` says the conversion does not depend on
*how* the inclusion was established — the C++ analogue of the fact that
admissibility is compile-time and erased. This is the cleanest
confirmation in the run that the "subsumption by implicit conversion"
decision costs nothing. **Letter 3.**

`emptyEquiv` and `map_emptyEquiv` (`Graded/Carrier.lean`) similarly
validate the ∅-grade-is-bare-`T` decision: the two are isomorphic and the
isomorphism is natural, so the C++ choice buys client-API ergonomics at
the price of a conversion, not of a law. **Letter 2.**

### 1.7 A facility P3200 does not have and could state cheaply

`Graded/Morphism.lean` builds error *renaming* — adapting a library's
error types to yours — and proves it commutes with everything:
`rename_pure`, `rename_bind`, `rename_ap`, `rename_map2`, `rename_map`,
`rename_widen`, `rename_cast`, `traverse_rename`, and
`rename_join`/`rename_bot` (it is a pomonoid homomorphism). `GradedHom`
requires neither injectivity nor surjectivity of the grade map.

Nothing in `#cpp-counterpart` mentions this, and it is the single most
obviously useful missing facility: every real program that composes two
libraries needs it. **Letter 10.**

### 1.8 Shape preservation is an extra promise, not a standard one

`traverse_length` (`Graded/Traverse.lean`) proves
`(traverse f xs).value().size() == xs.size()` — `#cpp-counterpart`'s one
traverse claim. It holds. But `#ungraded-baseline`'s Mathlib
correspondence table records that `LawfulTraversable` has **no** generic
shape-preservation axiom; it is specific to `List`'s own instance. So
P3200's shape-preservation promise is genuinely *additional* to the
standard traversable law set and must be stated separately rather than
inherited. **Letter 13.**

The same table records the reverse gap: Mathlib's `naturality` field (for
an `ApplicativeTransformation` between two genuinely different
applicatives) has **no** counterpart here. `widen` changes the grade of
the same functor and never relates `Graded g` to an unrelated `F`. If the
C++ design wants that law, nothing in this model covers it.

### 1.9 Ready to use: `docs/probe-harness.md`

53 probes, one per tabulated law that has a C++ equation, written against
`#cpp-counterpart`'s own names (`and_then`, `apply`, `transform`,
`flatten`, `widen`, `transpose`). Mechanically generated from
`docs/laws.json`, so it cannot drift from the proofs. This is a test file
for the C++ repo that needs translating, not designing. **Letter 15.**

---

## 2. Cross-step coherence

**Verdict: the model is coherent. Sixteen cleared workers built one artifact,
not sixteen.** The drift that exists is entirely in *prose about the code*,
never in the code itself, and it is all of one kind: a claim that was true
when written and that no later step was asked to revisit.

### 2.1 No fork, anywhere

The plan's hardest rule — never fork a shared definition — held completely.
Two `inductive` carriers exist in the whole tree: `Graded` (`Carrier.lean`)
and `Accum` (`Accum.lean`, planned, documented, not a fork). Everything
else that looks like a second carrier is an `abbrev` over `Graded`:

- `Comp g h α := Graded g (Graded h α)` (`ComposeApp.lean:51`)
- `Fixed g α := Graded g α` (`Ungraded.lean:47`)
- `Canon Err := { l : List Err // l.SortedLT }` — a subtype, and
  `docs/design.md#representation` opens by saying it is a representation
  theorem about `Grade`, not a second grade, before a reader can misread it.

No `Graded'`, no `GradeS`, no local `structure` wrapping `Graded`, no second
`widen`. `Accum.cast` and `Comp.castGH` exist but are the planned second
carrier's own transport and a derived double-cast helper respectively.

`Examples/Validation.lean` is the strongest single coherence signal in the
run: ten steps edited it, +423/-16, and the only 16 deletions are
[monad-laws] replacing the `REPLACED-BY: bind` block, exactly as the plan
said it would. A shared merge point touched by ten cleared workers, and
nobody rewrote anybody.

### 2.2 The at-most-one-error condition — the brief's real question, answered

The brief asked whether it is stated once as a named predicate or spelled
several ways. **It is spelled three ways, and there is no named predicate.**
There is no `def AtMostOneError`, no `isOk`/`isErr`, nothing. Each site
writes an anonymous `∨` of `∃`-equations bound to a local hypothesis name.

But the drift is smaller than that sounds, because the four sites are not
four spellings of one condition — they are four *different* facts, and
`docs/design.md#laws-inventory` already gets this exactly right:

| site | shape | verdict |
|---|---|---|
| `ap_flip` (`Applicative.lean:163`) | 2-way `∨`, `honeok` | **load-bearing**, counterexample in `Tests/Applicative.lean:62` |
| `Accum.toGraded_grade` (`Accum.lean:292`) | 2-way `∨`, `honeok`, same *form* over `Accum` | **not needed** — `toGraded_grade'` (`:321`) proves it unconditionally |
| `flatten_comm` (`Compose.lean:175`) | **no hypothesis** | vacuous: a nested carrier cannot hold two errors |
| `flatten_ap` (`ComposeApp.lean:382`) | **3-way `∨`**, `hcond`, asymmetric | a *different* condition, discovered during proof |

So the honest reading is: the model resisted the obvious over-generalization
in three of four places, and [oracle-export] caught it and wrote it up
correctly. What is missing is only the mechanical link — the two sites that
genuinely share a form (`ap_flip`, `toGraded_grade`) share it by
copy-and-docstring rather than by citation.

**One real rule violation here, in the other direction.**
`docs/RULES.md` says "a theorem takes the *weakest* hypothesis that proves
it." `Accum.toGraded_grade` deliberately keeps a hypothesis its own
docstring admits is "not, in the end, load-bearing," for parallelism with
`ap_flip`. That is a considered, documented deviation, not a slip — but it
is a deviation, it was not raised as an amendment, and both `toGraded_grade`
and `toGraded_grade'` now ship. My recommendation is to keep both and say
so at `#applicative`, because the *pair* is the finding; but the rule and
the artifact currently disagree and only the artifact knows it.

### 2.3 The one live contradiction: `join_comm`'s "second appearance"

[compose-applicative] wrote that `Comp.grade_reassoc` is "the second
appearance of `join_comm` in the whole model, after `ap_flip`." It was
wrong when written — `flatten_comm`, `joinAll_perm` and `join_mem_eq`
already used it — and it survives in **five places**:

- `Graded/ComposeApp.lean:347` (comment)
- `Graded/ComposeApp.lean:351` — **the `/-- -/` docstring on
  `Comp.grade_reassoc`**, i.e. it ships with the API
- `docs/design.md:783` (`#compose`)
- `docs/design.md:882` (`#graded-traversable-composition`)
- `docs/design.md:1609` — **inside [oracle-export]'s own paragraph headed
  "Commutativity: six sites, not three"**

The last one is the finding. [oracle-export] counted correctly, wrote the
correct number in bold as a section heading, and then repeated the wrong
claim four sentences later in the same paragraph, because it was copying
[compose-applicative]'s sentence rather than its own table. The true count
is six concrete sites plus the generic `joinAllG_perm`, or ten textual uses
including tests and the `IsCommPomonoid Grade` instance field.

This is exactly the drift a cleared worker cannot see, and it is worth
noting that the step *designed* to see it saw it and then reintroduced it.
A generated table beats a hand-written sentence; the sentence should be
deleted in all five places rather than corrected in four.

### 2.4 "Casts tolerable, not dominating" — half confirmed, half overtaken

[monad-laws] recorded the verdict at `docs/design.md#carrier` and marked it
"Standing, not revisited." Five law-heavy steps followed and none amended
it. Checking:

**The mechanism claim is exactly right and stood up completely.** Three
transport lemmas (`cast_ok`, `cast_err`, `cast_widen`, all in
`Graded/Monad.lean`, all proved `subst e; rfl`) absorb every cast. The
proof: `subst` appears in twelve proof bodies in all of `Graded/`, and **ten
of the twelve are inside a transport lemma's own body** (`cast_cast`,
`widen_cast`, `rename_cast`, the three in `Monad.lean`, three in
`Accum.lean`). The other two, `Traverse.lean:223,240`, substitute a `List`
equality obtained from `injection` — not a grade equality. **Not one law
re-derives cast bookkeeping.** Raw `▸` outside a definition body appears
three times (`Traverse.lean:164,173`, `Morphism.lean:239`). The discipline is
essentially perfect.

**The volume claim did not stand up, and nobody was positioned to notice.**
`cast` now occurs 264 times in `Graded/`; `ComposeApp.lean` alone holds 76 of
them, 29% of the total, in a module written three steps after the verdict.
And several proofs *are* dominated by bookkeeping in the plain sense of line
count:

- `flatten_comm` (`Compose.lean:175-191`): sixteen lines, **100% `change` +
  `rw [cast_ok]`/`rw [cast_err]`**, zero content lines.
- `bind_assoc` (`Monad.lean:83-106`): ~19 lines of `change` to 4 of `rw`.
- `Comp.traverseComp_cons` (`ComposeApp.lean:271-303`): 29 lines, no content
  line at all — the whole proof is cast normalization.
- `flatten_ap`, `flatten_flatten`, `Comp.ap_comp`: same shape.

And it has reached the *statements*. Counting through `Comp.castGH`
(`ComposeApp.lean:85`, two `Graded.cast`s) and `Graded.ap`
(`Applicative.lean:27`, itself a `cast`), `Comp.ap_interchange`
(`ComposeApp.lean:167`) carries **at least six** casts in one statement, and
`Comp.ap_comp` five or more, with two of its grade equalities written as
inline `by rw [...]` terms inside the statement. Most seriously, `GradedHom` (`Morphism.lean:181`) has
two *fields* that are cast-quantified equations — the cast burden is in the
interface, not only in the proofs.

**Judgment: the bind-at-sufficient-grade alternative named at `#carrier`
should be a follow-up run, and this review is the amendment
[monad-laws] could not have written.** The verdict was correct on the
evidence available at step 5 (five monad laws, one grade coordinate). It
does not describe a two-coordinate composite carrier. The cost is not proof
fragility — the transports hold — it is that the statements a C++ reader is
supposed to recognise have become unreadable, which is the one thing this
whole model exists to avoid. `Comp.ap_interchange` should be legible as the
interchange law and is not.

Note also `Graded/Tuple.lean`, `Canonical.lean` and `Obligations.lean` are
entirely cast-free and read as ordinary Lean. The burden is exactly
co-extensive with the carrier-law modules.

### 2.5 The lattice-instance decision is honoured, and rests on a false premise

No Mathlib `Lattice`/`SemilatticeSup`/`PartialOrder`/`OrderBot` instance is
declared for `Grade` anywhere. The `#grade` provisional is kept to the
letter. Two things complicate it:

1. **`Grade` is an `abbrev` for `Finset`** (`Grade.lean:13`), and
   `Mathlib.Data.Finset.Lattice.Lemmas` is imported. I checked this in Lean
   rather than inferring it: `#synth Lattice (Grade E)`,
   `SemilatticeSup`, `PartialOrder` and `OrderBot` **all resolve**, to
   `Finset.instLattice`, `Finset.instLattice.toSemilatticeSup`,
   `Finset.instPartialOrder` and `Finset.instOrderBot` — with no declaration
   in this repo. And
   `example (g h : Grade E) : Grade.join g h = Grade.join h g := by unfold Grade.join; exact sup_comm ..`
   compiles: a proof can reach Mathlib's lattice API for a `Grade` fact
   today, citing no named `Grade` lemma. The decision's stated rationale —
   "an instance would let `simp` reach for these properties invisibly, which
   defeats the point of naming them" — describes a protection the design
   never had. What actually preserved greppability was worker discipline
   (§2.6), not the absence of an instance.

2. **[grade-obligations] registered three structure instances *on* `Grade`**
   (`Obligations.lean:146,158,162`), reproducing at one remove exactly the
   simp-reachability the provisional declined — and doing so is the right
   call for that step, which needs the instances to state the obligation at
   all. But `#grade`'s provisional and `#obligations`' instances now sit in
   tension and neither section mentions the other on this point.

**Recommendation: rewrite the `#grade` provisional.** The decision to keep
citing named lemmas is right and worked; the reason given for it is not the
reason it worked.

### 2.6 The things that held cleanly

- **Named-lemma citation.** `Finset.union_*` appears **only** in
  `Graded/Grade.lean:25,29,33,37,41`. No module re-proves a union law
  inline; `simp [Finset.ext_iff]`, `ext` and `aesop` on Finsets appear
  nowhere in the repo. Given that Mathlib's whole `Finset` lattice API was in
  scope the entire time (§2.5), this is discipline, and it is the property
  the whole `laws.md` inventory depends on.
- **`docs/laws.md` agrees with the tree, provably.** 146 theorems in
  `Graded/*.lean`, 146 rows in `laws.md`. Not a sample — every theorem. `make
  laws` regenerates and `git diff --exit-code`s, so it cannot drift.
  `scripts/laws-inventory.py`'s allow-list is per-entry with a stated reason
  from one of exactly two accepted categories, and `#laws-inventory`
  documents the heuristic's own three blind spots (a `def` that bakes a
  property into a cast; `flatten_ap`'s citation via `grade_reassoc`;
  `foldG_le`'s class hypothesis vs its proof text) rather than hiding them.
  This is the best-built artifact in the run.
- **`docs/design.md` is still by-anchor.** 16 `##` sections, each exactly
  once, no duplicates, no dated log inside any of them. The `#carrier`
  provisional carries [monad-laws]'s verdict *in place* rather than as an
  appended entry — the right pattern. Question sections
  (`graded-traversable-composition`, `grade-join-strength`) live as `###`
  under their owning anchor with Question / Status / Why / Log, which matches
  the house decision-log convention.
- **`#cpp-counterpart` was never edited by a worker.** Every step read it by
  anchor and reported against it. That firewall held.

### 2.7 Three defects to fix in `docs/design.md`

1. **`#provisional-decisions` misses `#grade`.** There are five
   `> **Provisional.**` marks in the file (lines 23, 98, 134, 336, 989). The
   index lists four of them plus two OPEN questions — and the one it omits is
   line 98, `#grade`'s "no Mathlib lattice instance," which is the provisional
   this review most needs a reader to find (§2.5).
2. **The index lists `graded-traversable-composition` as an OPEN question
   with text saying "whether a `Compose`-aware version is worth building is
   undecided."** The section itself says **CLOSED**, and
   [compose-applicative] *built* the Compose-aware version. Both halves of
   the index entry are now stale. (Flagged by [blog-series-edit] and
   correctly judged out of its scope.)
3. **`#obligations` has a "Judgement call 2, restated" heading whose content
   is judgement call 1** (nesting vs. sibling). Cosmetic; one word.

### 2.8 `Tests/` — one substantive gap

No `sorry`, no `native_decide`, no commented-out `example` or `#guard`
anywhere. Three tests are vacuous where distinct grades were available, one
of them materially:

- **`Tests/ComposeApp.lean:123-127` — the material one.** `flatten_ap` is
  instantiated with `xx := Comp.pure a`, so its cast is
  `Comp.grade_reassoc {E.parse} ⊥ {E.range} ⊥`, whose `join_comm` step is
  `join {E.range} ⊥ = join ⊥ {E.range}` — both sides collapse by the *unit*
  laws. **`Comp.grade_reassoc` exists to be the model's commutativity site,
  and no test in the tree exercises its commutativity.** Four distinct
  grades would fix it.
- `Tests/Morphism.lean:43-46` — `rename_cast` at `e : {E.parse} = {E.parse}`,
  so both casts are `rfl` and "rename commutes with cast" is tested where
  there is nothing to commute past. `{E.parse, E.range}` is in scope at
  `:38`. Contrast `Tests/Monad.lean:5-8`, whose docstring says `bind_assoc`
  was deliberately instantiated at three *distinct* grades "so the `cast` it
  produces is genuinely a transport, not `cast rfl`" — the discipline exists
  in the project and this site missed it.
- `Tests/Tuple.lean:32-35` — `sequence_cons` on a one-element `GList`, so the
  heterogeneity that is the module's whole point is never exercised.

Separately, `docs/RULES.md` asks for an `example` instantiating **every**
theorem of the step, and about ten have none — including `cast_ok`,
`cast_err` and `cast_widen`, the three transport lemmas §2.4 shows the whole
model rests on.

### 2.9 `PROPERTY:` tags — the brief's premise was wrong, and there is still a gap

The convention is not "every property lemma is tagged." Nine `PROPERTY:`
tags exist (seven in `Grade.lean`, two in `Morphism.lean`) and they mark
*property definitions* for `laws-inventory.py` to grep, not laws. Laws use a
parenthetical docstring marker instead — `(unit)`, `(associative)`,
`(order)` — 28 of them.

Within that real convention, two gaps:

- **`Canonical.lean`'s `canonEquiv_union` (`:143`) and `canonEquiv_bot`
  (`:151`) are homomorphism laws of exactly the shape that *is* tagged
  `PROPERTY: homomorphism` in `Morphism.lean:36,41`, and are untagged.**
  Same shape, tagged in one file and not the other — the sharpest tagging
  inconsistency in the tree.
- **`scripts/laws-inventory.py:60-72` carries a hardcoded `ORDER_SUPPLEMENT`
  dict re-adding five untagged `Grade.lean` order lemmas.** A tool patching a
  tagging gap is a signal the tags belong on the lemmas.

Also `Obligations.lean` restates all seven properties as class fields and
tags none, which is why `foldG_le`'s row in `laws.md` reads `order` when its
class hypothesis is `IsIdemPomonoid` — a divergence `#laws-inventory`
honestly documents rather than papers over.

### 2.10 One place `docs/RULES.md` and the artifact genuinely disagree

`Canonical.lean` violates "never re-prove a `Finset` fact inline" in three
places, one of them squarely:

- **`Canonical.lean:147`** — `rw [..., Grade.join]` **unfolds the named
  definition** to raw `Finset.union` to close the goal. That is the exact
  move `docs/RULES.md` forbids, in the file whose job is to carry
  `Grade.join` across `canonEquiv`.
- `Canonical.lean:117` — `def union := ofFinset (toFinset c ∪ toFinset c')`
  uses raw `∪` rather than `Grade.join`.
- `Canonical.lean:77` — the docstring above it claims the proof "cites
  `Finset.sort_toFinset` **by name** rather than unfolding"; the proof is
  `simp [toFinset, ofFinset]`, which unfolds both and lets `simp` find it.
  **The docstring and the proof disagree.** That one is worth fixing on
  principle: a false docstring is worse than an untidy proof.

`Morphism.lean` and `Carrier.lean` also touch `Finset` directly, but for
facts with no `Grade`-named counterpart to cite (`Finset.image*`,
`Finset.notMem_empty`) — benign, and `rename_mono`'s docstring documents its
own shortcut rather than hiding it.

---

## 3. Context discipline

**Held, with three small leaks and one structural gap.**

**The central firewall worked completely.** `codebase-map.md` is referenced
by **zero** `step-*.md` and **zero** `handoff-*.md`. The only references are
`AGENT-PROMPT.md`'s prohibition, `README.md`'s description, and this file.
No step file grew a survey section — grep for `survey|I surveyed|walk the
tree|read the whole|full listing` over all 17 step files returns nothing.
That is the failure mode the consult-tier split exists to prevent, and it
did not occur once.

**Handoffs: all 18 under budget**, 14-104 lines against a ~150 ceiling, ~30%
headroom throughout.

**Step files: no logs.** Three dated lines exist, all one to three lines at
the top, all forward-justifying. Correction to my own brief's assumption:
the third is `step-grade-obligations.md:11`, not `step-compose-applicative.md`
— the latter was *created whole* by the amendment commit and carries no
dated block. Line counts cluster at 164-184 for thirteen files; the four
outliers (262-334) are the bootstrap step plus all three late-added steps,
which is exactly where extra length is expected. **Zero step files written
in the original plan and executed as written exceeded 184 lines.**

**Three genuine leaks:**

1. **`handoff-grade-pomonoid.md:49-54`** carries a "Warm verify time" section
   with wall-clock numbers *and a pointer into `metrics.jsonl`*, which
   `AGENT-PROMPT.md` declares write-only. The timings are arguably
   forward-useful; the pointer has no forward use at all.
2. **Three handoffs carry a section headed, verbatim, `## One finding not
   needed by this step, recorded for completeness`** —
   `handoff-traverse-list.md:60`, `handoff-traverse-tuple.md:85`,
   `handoff-compose-flatten.md:97`. Each concedes in its own text ("if you're
   curious", "has no bearing on"). This is the archivist reflex the
   forward-only rule exists to suppress, and the identical heading in three
   independent steps means it **propagated by imitation** down the handoff
   chain. That is the interesting part: a cleared worker cannot copy a habit
   it has not seen, so the one file each worker *does* read is the vector.
   Worth a line in `AGENT-PROMPT.md`.
3. **Three handoffs point at files the recipient may not open**
   (`handoff-applicative-accumulation.md:89`, `handoff-monad-laws.md:64`,
   `handoff-applicative-from-monad.md:65`). Low severity — each restates the
   content inline, so the citation is provenance, not a dependency — but it
   models the wrong habit.

Against those, `handoff-ungraded-baseline.md:52-62` is a model of the
discipline, telling the recipient what to **exclude**: "Do not fold
`flatten_ap` into your table; it is not one of the laws in your declared
scope … mentioning it would blur the exact row your step 4 wants."

**The letters.** Numbering is gap-free 0-15 with `closing.org` = 16;
`index.org` lists all 17 in order; `#+SERIES_PREV`/`NEXT` chains end to end
with no breaks. Every internal back-reference is arithmetically correct
against the *final* numbering ("Sixteen letters ago", "Fourteen letters
ago", "none of those eleven letters") — so [blog-series-edit]'s renumbering
was done by reading, not by `sed`. Register: 17/17 on `Steve,`, 17/17 on
`--SMD`, **zero** U+2014 em-dashes (also zero en-dash, horizontal bar,
minus). Zero occurrences of `agent`, `orchestrator`, `token`, `metrics`,
`Sonnet`, `Claude`, `LLM`, `handoff`, `worker`, `tmp/plan`.

**Three letters leak the machinery, each by one word**, all the same tell in
three spellings: `graded-carrier.org:44` ("as short as **the step file**
predicted"), `subsumption-widen.org:38` ("**The step plan** … told me to
budget several attempts"), `canonical-representation.org:27` ("**The step
brief** told me to build"). Each is a one-line fix by attributing the
prediction to the writer ("I expected this to be short"). Also every letter
carries `#+STEP: <slug>` metadata, and `closing.org:4` reads
`#+STEP: blog-series-edit` — worth deciding whether those keywords survive
publication.

The one *number* in a letter (`baseline-capture.org:91-97`) is deliberately
blurred — "a little over two minutes", "well under fifteen seconds" — against
the handoff's precise "4 seconds / 12 seconds". That is the right instinct
and it was applied on purpose.

**No letter carries a bracketed forward-reference note.**
[blog-series-edit] checked and judged none were needed, and for the
at-most-one-error correction it is right — `oracle-export.org:81-93`
corrects the writer's own earlier narration in place, which works.

For the composition reversal I part company with it, mildly.
`compose-flatten.org` (Letter 9) is honest and its C++ takeaway — two
different algorithms, and flattenability does not tell you which you wrote —
survives Letter 12 completely, so nothing in it is *wrong*. But `index.org:11`
promises "where a later letter corrects an earlier one, the earlier letter
says so in place," and `closing.org:96` calls this the series' one real bug.
A reader who stops at Letter 9 believes the composition-law question is
settled negatively; it is settled *positively*, in the right form, three
letters later. One bracketed line in `compose-flatten.org` redeems the
index's promise. Low priority, but it is the promise the series makes about
itself.

**A latent defect, found and fixed by this review.**
`scripts/check-letters.sh` required a `blog/letters/<slug>.org` for *every*
checked checklist item, exempting only `blog-series-edit`. So marking
item 18 — this review — turned the tree **red**: `check-letters: missing
letter: blog/letters/integration-review.org`. The exemption category
already existed and already had the right comment ("its output is the index
and the closing letter, not a per-step letter"); `integration-review` is
the same category and was simply not in it. Nobody could have hit this
before now, because item 18 is the first non-letter step after
`blog-series-edit`. Fixed here by extending the exemption to a `case`
covering both slugs; `make all` re-run green afterwards.

**A second structural gap, not closed:** `scripts/check-letters.sh` enforces
the four headings and index completeness, but **not** the salutation, the
signature, or em-dash absence. The register currently holds by manual sweep
— and that sweep already silently missed six of sixteen files once
(commit `e1fa465` covered ten letters, and the record initially said
sixteen). Three greps in that script make the current clean state durable
and would have caught the original miss.

---

## 4. Metrics

Promoted. `metrics/fanout-runs.jsonl` created, 19 rows, each tagged
`run: lean-model-1`, `branch: integration/lean-model`. The
`grade-obligations` row with `wall_seconds: 1788879160` is retained and
marked `superseded: true` with a reason rather than dropped. Rows from the
first four steps carry `attempts_comparable: false` (§4.3). The
`oracle-export` row carries a `diff_note` (§4.2).

**This run is the baseline. There is no prior calibration, so what follows
is a floor and a first sizing table, not a comparison.**

### 4.1 Whole run

| | |
|---|---|
| steps | 17 implementation + 1 `verify-floor` |
| total wall | **17760 s ≈ 4.93 h** |
| mean / median step | **1045 s (17.4 min) / 937 s (15.6 min)** |
| verify wall, total | **234 s** |
| **verify as a share of the run** | **1.3 %** |
| diff | +10393 / −251 (branch total +12509 / −112 incl. plan files) |
| outcomes | 16 green, 1 blocked (partial), 0 amendments |
| `out_of_scope` | **empty on every row** |

**The single most important number: verify is 1.3 % of the run.** The
brief anticipated "cheap edit gated by a long `lake build`" as a failure
mode. In this repo, at this size, it does not exist. `make verify` warm is
1-5 s and the `verify-floor` row records 4 s warm, 12 s cold, after a
one-time ~150 s `lake exe cache get` for 8747 Mathlib files. The cost of a
step here is **thinking about a proof**, not checking it.

There is exactly one exception, and it proves the rule: [monad-laws] at
173 s verify (13.2 % of its own step) — the first step to pull in enough of
Mathlib to force a real rebuild. Every later step ran warm at 0-23 s.

### 4.2 Per step

| step | wall s | verify s | v% | files | +/− | log B |
|---|---|---|---|---|---|---|
| baseline-capture | 780 | 4 | 0.5% | 30 | 564/71 | 222 |
| grade-pomonoid | 340 | 5 | 1.5% | 6 | 259/1 | 745 |
| graded-carrier | 477 | 3 | 0.6% | 9 | 325/2 | 2571 |
| subsumption-widen | 362 | 2 | 0.6% | 7 | 277/1 | 542 |
| **monad-laws** | 1312 | **173** | **13.2%** | 7 | 374/17 | 458 |
| applicative-from-monad | 1018 | 2 | 0.2% | 7 | 481/2 | 1430 |
| applicative-accumulation | 1549 | 2 | 0.1% | 8 | 708/2 | 1020 |
| traverse-list | 725 | 3 | 0.4% | 7 | 502/2 | 1191 |
| traverse-tuple | 1145 | 4 | 0.3% | 9 | 499/3 | 1507 |
| compose-flatten *(blocked)* | 2043 | 4 | 0.2% | 7 | 508/1 | 3044 |
| graded-morphism | 937 | 1 | 0.1% | 7 | 607/1 | 3341 |
| canonical-representation | 453 | 4 | 0.9% | 7 | 404/2 | 3367 |
| **compose-applicative** | **2500** | 23 | 0.9% | 7 | 946/33 | 3816 |
| ungraded-baseline | 634 | 2 | 0.3% | 6 | 691/0 | 3667 |
| grade-obligations | 915 | 1 | 0.1% | 6 | 705/0 | 3667 |
| oracle-export | 1484 | 0 | 0.0% | 8 | **2244**/4 | 3667 |
| blog-series-edit | 1086 | 1 | 0.1% | 20 | 299/109 | 3682 |

`log_bytes` grows monotonically 222 → 3682 as modules accumulate; it is a
proxy for tree size, not for step difficulty, and should not be read as one.

### 4.3 The hottest steps, and which fix each needs

The brief names two failure modes with opposite fixes. Both appear, plus a
third the brief did not anticipate.

**Split these — genuinely oversized.**

- **`compose-applicative` (2500 s, 979 lines, ~15 cheap builds) — the
  hottest step in the run.** It built a new composite carrier, four
  applicative laws over it, `traverseComp`, the composition law, *and*
  `flatten_ap` with a hypothesis discovered mid-proof. That is two steps.
  A natural cut: `Comp` + the four applicative laws (which are mechanical
  once `Comp.ap` exists), then `traverseComp_eq` + `flatten_ap` (which is
  where the discovery is). The second half is the interesting one and it
  ran last, on a tired context.
- **`applicative-accumulation` (1549 s, 710 lines).** A whole second
  carrier plus a full law set plus `notMonad`. `notMonad` is an
  impossibility proof and deserved its own step.
- **`grade-obligations` (915 s, 705 lines)** and **`ungraded-baseline`
  (634 s, 691 lines)** are large-diff but came in fast, because both are
  restatements over machinery that already existed. Large diff alone is not
  the signal; large diff on *new* machinery is.

**Narrow the verify target — exactly one step.**

- **`monad-laws` (1312 s, 391 lines, 13.2 % verify).** The one genuinely
  verify-gated step. The worker already applied the fix without being told,
  iterating on `lake build Graded.Monad` and running full `make verify` four
  times. Worth promoting from worker initiative to the step template:
  **`lake build Graded.<Module>` for the edit loop, full `make verify` once
  at the end.** Note this step also burned three failed attempts on
  `bind_assoc`'s cast bookkeeping — which is §2.4's problem showing up in
  the clock.

**Neither fix applies — the third mode.**

- **`compose-flatten` (2043 s, blocked).** Not oversized and not
  verify-gated. It spent 34 minutes proving a theorem false because the
  step file asked the wrong question — the flattened composition law
  instead of the product-graded one. **That is the cost of a mis-specified
  step: ~34 minutes plus the whole of `compose-applicative`'s 42 minutes to
  ask it again correctly.** No decomposition fix reaches it; the fix is at
  planning time, and the plan has since applied it (the dated amendment in
  `step-compose-flatten.md` exists precisely so a re-run cannot repeat the
  substitution).
- **`oracle-export` (1484 s, 2248 lines).** Biggest diff in the run by 2.3x
  and it means nothing: 2244 of those insertions are *generated*
  (`laws.md` 22 KB + `laws.json` 11 KB + `probe-harness.md` 10 KB). The
  hand-written diff is one Python script and one `design.md` section.
  **Metrics defect: `diff` should exclude or tag generated output**, or every
  future calibration will read a codegen step as the largest change in its
  run. Tagged in the promoted rows.

### 4.4 `attempts` is not a usable field, and the fix is a rename

Three workers used three conventions before the definition was fixed, so the
first four rows are not comparable and are marked as such. But the deeper
problem survives the fix: **`AGENT-PROMPT.md` never defines `attempts` for
the metrics row at all.** It only says "after 3 genuinely different attempts
without GREEN, stop." Workers reasonably recorded "`make verify` runs
intending GREEN," which is a *different quantity* from the one the stop rule
counts.

The consequence is that **nothing in `metrics.jsonl` measures the stop
rule.** `compose-flatten` records `attempts: 3, outcome: blocked` with all
three verifies at exit 0 — incoherent from the row alone, and only the
`note` rescues it. Meanwhile the genuinely useful number lives in prose in
every note: the cheap targeted `lake build` iterations, **3 to 16 per
step**, which track wall time far better than `attempts` does
(`compose-flatten` 16, `compose-applicative` 15, `applicative-from-monad`
12, `graded-morphism` 10; against `traverse-list` 3, which was green first
try).

**Fix for run 2 — split one field into three:**

- `verify_runs` — full `make verify` invocations. Mechanical, comparable.
- `edit_iterations` — cheap targeted builds. This is the effort proxy.
- `proof_attempts` — genuinely different approaches to a stuck goal. **This
  is the one the stop rule counts, and the only one that should be called
  `attempts`.**

Also worth adding: `verify_seconds_cold` vs `_warm`, since the 173 s vs 1 s
split is entirely first-touch-of-Mathlib and is invisible in the current
field.

### 4.5 Content of the project memory entry

Written here rather than to memory, per instruction. For "Where the
measurements accumulate":

> **`lean-graded` — graded Transpose Lean model. Baseline run
> `lean-model-1`** (`metrics/fanout-runs.jsonl`, branch
> `integration/lean-model`, 17 cleared Sonnet steps, 2026-09-07/08).
>
> **What a step costs.** Median 15.6 min, mean 17.4 min, 4.9 h total.
> Range 340 s (a small algebra module) to 2500 s (a new composite carrier
> plus its full law set). Diff 260-980 lines per step, ~10.4 k insertions
> and 251 deletions across the run — near-monotone growth; the "extend in
> place, never fork" rule showed up as an almost total absence of
> deletions.
>
> **Which verify command dominates: none.** `make verify` (= `lake build`,
> three libs) is **1.3 % of total wall time**. Warm floor 1-5 s, cold 12 s,
> after a one-time ~150 s `lake exe cache get` (8747 Mathlib files;
> *without* the cache a build is hours and is a block, not a wait). The one
> exception is the first step that pulls in significant Mathlib — here
> `monad-laws` at 173 s, 13.2 % of its own step; every later step ran warm.
>
> **Edit/verify split: roughly 98.7 / 1.3.** The cost of a step in this
> repo is authoring a proof, not checking it. The right edit loop is
> `lake build Graded.<Module>` (sub-second to seconds) with one full
> `make verify` per step; workers averaged 3-16 such targeted builds per
> step and that count predicts wall time far better than `make verify`
> counts do. Do not optimise the verify target here — optimise step size.
>
> **Amendments: none.** No `amendment-*.md` was ever written. One partial
> block (`compose-flatten`), resolved by adding a step rather than by
> amending an existing one. Zero forks, zero `out_of_scope` entries on any
> row. Three steps were added mid-run at the owner's request
> (`compose-applicative`, `ungraded-baseline`, `grade-obligations`).
>
> **Metrics-schema debt to fix before run 2.** `attempts` conflated three
> quantities and never measured the stop rule it was named for; split into
> `verify_runs` / `edit_iterations` / `proof_attempts`. `diff` must exclude
> or tag generated output — `oracle-export`'s 2248-line diff is 2244 lines
> of script output and reads as the largest change in the run.

---

## 5. Process: the three orchestrator decisions

### 5.1 The `compose-flatten` partial-block ruling — right, and the best call in the run

The step brief said: write the unprovable theorem with a `sorry`, do not
commit, file a blocked report. The ruling was: commit everything genuinely
proved with no `sorry` in the tree, file the block for the one law, do not
mark the checklist, halt for a human.

**Correct, and the brief was wrong.** The brief's instruction would have
discarded eight proved laws (`flatten_eq_bind_id`, `flatten_map`,
`flatten_pure_outer`, `flatten_pure_inner`, `flatten_flatten`,
`flatten_widen_outer`, `flatten_widen_inner`, `flatten_comm`), `swap`,
`Tests/Compose.lean`, the `Examples/Validation.lean` consumer and a letter,
to punish one false conjecture. It would also have put a `sorry` in a tree
whose entire verification story is "no `sorry` survives a commit" — the
brief was asking for a violation of `docs/RULES.md` in order to comply with
`AGENT-PROMPT.md`, and the ruling resolved the conflict in favour of the
invariant that everything else depends on.

The three things that make it defensible rather than merely convenient:

1. **The result was strengthened, not weakened.** The worker did not fail to
   prove the law; it *refuted* it, with an `#eval`-confirmed counterexample
   and a stated mechanism. "Blocked" undersells what happened.
2. **The checklist was not marked and a human was asked.** The ruling kept
   the halt.
3. **Marking it done only after the finding was recorded as a named open
   question was the right sequencing.** The question outlived the block —
   `graded-traversable-composition` is now CLOSED with both halves settled,
   and the link from `checklist.md:20` still resolves, which is exactly what
   naming a question rather than a conclusion buys.

The one thing I would do differently: the *later* orchestrator checks
(re-running at a single grade; separating "flattened form false" from
"product-graded form untested") were the real intellectual work, and they
happened after the fact, in a context the plan does not have a slot for. If
a step refutes something, a short verification consult should be part of the
block protocol, not an improvisation. Note that both checks are recorded in
`blocked-compose-flatten.md` under headings that say "orchestrator, after
the fact" — honest, and the right way to record it.

### 5.2 The two harness changes — both correct, and the `nosorry` one is the run's most important finding about process

**`make nosorry` passing unconditionally: unambiguously a fix, and the
scariest thing in the run.** The check searched `Graded Tests Examples`
where two were root *files*, `grep` exited 2 (error, not "no match"), and
the shell's `!` converted the error into success. A planted `sorry` passed.
For two steps the project's central invariant was not being checked at all.

The current Makefile fixes it properly: it enumerates files with `find`,
asserts the list is non-empty, and **switches on `grep`'s exit code with an
explicit `*)` arm** that fails on anything other than 0 or 1. That is the
right shape — the bug was that an error was indistinguishable from a pass,
and the fix makes them distinguishable by construction rather than by luck.

**But the part worth a paragraph is not the bug. It is that
`baseline-capture` found the symptom, tested it, reasoned confidently, and
concluded exactly backwards** — that the stderr noise was cosmetic and the
test passed anyway. Its own metrics note still contains the wrong reasoning:
*"`!` negation still yields nosorry=0 correctly since no sorry exists."* The
premise is true and the conclusion does not follow: the test passed
*because* the negation manufactured a pass, and would have passed with a
`sorry` present. That conclusion then went into a handoff as advice to
disregard the signal.

The lesson generalises past this run: **a cleared worker that finds its
verification tooling behaving oddly has no way to distinguish "this check is
noisy" from "this check is not running."** It has no history, no second
opinion, and a strong incentive to conclude the former. This is not a worker
defect — it is the one thing the fan-out architecture structurally cannot
do. The mitigation is cheap and should be standard: **`baseline-capture`
should plant a `sorry`, confirm `make nosorry` fails, and remove it.** A
verification harness that has never been observed failing has not been
tested. Commit `71e2de8` ("Correct the grade-pomonoid handoff on the nosorry
fix") shows the wrong conclusion had already propagated one step before it
was caught.

**`grep -q "error" build.log`: correct to remove.** It produced a *false
failure* on a green build because a lint warning quoted a docstring reading
"a finite set of error kinds." That is worse than the first bug in one
specific way: a check that fails when nothing is wrong trains everyone to
ignore it, and `lake`'s exit status is a real signal that the grep was
shadowing. Removing it and keeping `|| { tail -n 20 build.log; exit 1; }` is
right. The residual gap is that warnings are now invisible to `make verify`
— acceptable here (§5.3 reduces them to zero), but if warnings ever matter,
the fix is `lake build 2>&1 | grep -c warning` as a *separate* target, not a
substring match on the whole log.

### 5.3 Disabling three Mathlib lint rules — hygiene, not lost signal, and it is not close

All three disabled rules were **false positives by construction**, and the
lakefile documents each with its reason at the point of disabling:

- `style.header` wanted a Mathlib copyright block in every file. This is not
  Mathlib.
- `hashCommand` forbade `#guard`, which `docs/RULES.md` **requires** in every
  test module ("at least one `#guard` or `decide` that *computes*, so the
  definitions are known to reduce and not just typecheck"). Keeping this rule
  meant the project's own test convention would warn on every test file.
- `dupNamespace` flagged `Graded.Graded`, the name the plan specifies.

None of the three can ever fire on a real defect *in this project*, so
thirteen warnings on a green build were thirteen guaranteed false positives,
and thirteen guaranteed false positives is worse than none: it is the state
in which nobody reads warnings. Turning them off restored the possibility
that a *fourteenth* warning would mean something.

Three qualifications, none of which change the verdict:

1. The rest of `mathlibStandardSet` is still on
   (`weak.linter.mathlibStandardSet = true`), so this is a three-rule
   exception, not a blanket opt-out. That is the right granularity.
2. It is worth noting that these rules *earned their keep before they were
   disabled*: `grade-pomonoid`'s metrics note records that a missing module
   docstring tripped `style.header`, which is how the missing docstrings were
   found — and, via the quoted warning text, is also what triggered the
   `grep "error"` false failure in §5.2. One rule found a real gap and
   simultaneously exposed a harness bug, then was retired. Good innings.
3. §5.2's removal of the log grep means `make verify` no longer surfaces
   warnings at all. With the noise now zero, that is safe; the two changes
   are only jointly safe, and neither section mentions the other. Worth one
   line at `docs/design.md#toolchain`'s "Lint configuration" subsection.

### 5.4 The amendment record: zero, and I read it as decomposition quality

No `amendment-*.md` exists. One partial block, no forks, `out_of_scope`
empty on all 17 rows. The brief asks whether that means the decomposition
was well-sized or that workers were too reluctant to raise one. **Mostly the
former, with two specific near-misses that should have been amendments and
were not.**

The evidence for well-sized: ten of seventeen steps ran green within two
full verifies (and `attempts` overcounts, §4.4); `out_of_scope` is empty everywhere; ten steps
appended to one shared file without one rewriting another's work; and the
plan's own prediction record was *wrong* in at least six places
(`widen_cast` "will be fiddly" — closed by `subst e; rfl` immediately;
`toGraded_grade`'s hypothesis; `flatten_comm`'s expected hypothesis;
commutativity "three sites"; the idempotence count; `foldG_le`'s class) and
each wrong prediction was absorbed by the step that hit it, recorded, and
did not cascade. A brittle decomposition does not survive six wrong
predictions without one amendment.

**The two that should have been amendments:**

1. **`grade-obligations` needed a *stronger* hypothesis than its brief
   allowed.** `foldG_le` was predicted to need `Pomonoid`; it needs
   `IsIdemPomonoid`. `docs/RULES.md` is explicit: "If the proof needs more
   than the step allowed, that is a finding, not a licence: halt with an
   amendment (the design may be wrong) rather than strengthening the
   hypothesis silently." The worker strengthened it and documented it
   loudly — `#obligations` has a whole subsection headed "The layer-to-law
   table, and where the brief was wrong," and it is the best writing in the
   document. It was not silent, and the finding *is* the deliverable. But by
   the rule it was a halt, and the fact that the resulting work is excellent
   is not evidence the rule was wrong — it is evidence this worker was good.
   The orchestrator opening `grade-join-strength` afterwards is the
   amendment consult that should have been convened at the time; note it
   found something the worker had not (that `join_le` + antisymmetry
   *proves* `join_idem`, which reframes the entire three-layer story).
2. **`Accum.toGraded_grade` kept a hypothesis it did not need** (§2.2) —
   the same rule in the opposite direction. Also documented, also not
   raised.

So both directions of "hypothesis discipline" were bent by different workers
in the same run, each with a good local reason, neither escalated. **That is
the recognisable shape of an escalation channel that is technically
available and practically unused**: `AGENT-PROMPT.md` describes amendments
as costing a halt, and gives no cheaper option between "absorb it and write
a good paragraph" and "stop the run." A worker with a finding and a working
proof will always take the first.

**Recommendation for run 2:** add a third outcome between green and
blocked — a `finding-<slug>.md` that a worker writes *and continues*, which
the integration review is required to read. It costs no halt, it creates the
record, and it would have caught both of the above at the moment they were
live rather than at review. The one partial block in this run was already,
in substance, that third thing; the ruling in §5.1 invented it under
pressure. Make it a first-class outcome.

---

## 6. What to fix, ranked

Nothing here blocks merge. The branch is green, sorry-free at the kernel,
and internally consistent.

**Should fix — false or misleading claims in shipped text**

1. Delete the "second appearance of `join_comm`" sentence in all five places
   (§2.3), including the `Comp.grade_reassoc` docstring. It is false and one
   copy sits inside the paragraph that corrects it.
2. Add `#grade` to `#provisional-decisions`, and correct the
   `graded-traversable-composition` entry from OPEN to CLOSED (§2.7).
3. Fix `Canonical.lean:77`'s docstring, which claims a citation the proof
   does not make (§2.10).

**Should fix — a real test gap**

4. Instantiate `flatten_ap` at four distinct grades so
   `Comp.grade_reassoc`'s commutativity is actually exercised (§2.8). Today
   the model's second commutativity site has no test that uses
   commutativity.

**Worth a follow-up run**

5. **Reopen the bind-at-sufficient-grade alternative at `#carrier`** (§2.4).
   The transports hold, but `Comp.ap_interchange` carries six casts in one
   statement and `GradedHom` has cast-quantified *fields*. The verdict
   "tolerable, not dominating" was right for one grade coordinate and does
   not describe two.
6. **Answer `grade-join-strength`** (§1.4). This is the owner's call, not a
   worker's, and every "needs idempotence" row in `laws.md` changes character
   with the answer.

**Process, for the next fan-out**

7. `baseline-capture` must plant a `sorry`, watch `make nosorry` fail, and
   remove it. A harness never observed failing has not been tested (§5.2).
8. Split `attempts` into `verify_runs` / `edit_iterations` / `proof_attempts`
   and tag generated output in `diff` (§4.4, §4.2).
9. Add a `finding-<slug>.md` outcome that does not cost a halt (§5.4).
10. Add salutation / signature / em-dash greps to
    `scripts/check-letters.sh` (§3). (Its other defect — every checked
    checklist item demanding a letter, which made marking item 18 turn the
    tree red — is already fixed in this commit.)
11. Fix the three letter leaks — "the step file", "the step plan", "the step
    brief" — by attributing the prediction to the writer (§3).

---

*Integration review complete. Checklist item 18 may be marked.*
