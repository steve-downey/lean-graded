# Review of, and counter-plan to, `lean-model-improvements.md`

Written 2026-09-09 against `integration/lean-model` at `c9147eb`. Every
claim below was checked against the tree, not against the outline's own
prose. Line and count evidence is given inline so a later reader can
re-run the check rather than trust the sentence.

The outline is good. Its nine problems are real, seven of them verified
here without qualification. What it lacks is a sense of price: it
sequences a two-line docstring fix that removes a false claim from the
repository alongside a payload refactor that touches 175 pattern-match
sites and a C++ phase gated on an artifact that does not exist in this
repository — and it presents them as phases of one thing. The counter-plan
in §5 keeps almost all of the outline's content and re-sequences it by
evidence-per-unit-of-churn, with a gate after each tranche.

---

## 1. Verification of the outline's nine problems

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| 1 | `Pomonoid` documented as a partial order, defines a preorder | **Confirmed** | `Graded/Obligations.lean:95-106` — fields are `le_refl'`, `le_trans'`, no `le_antisymm`; docstring line 95 says "A partially ordered monoid", module docstring line 17 says "the textbook 'partially ordered monoid'". The *name* carries the false claim, not just the prose. |
| 2 | Fold equality confused with semantic reachability | **Confirmed, and worse than stated** | The overclaim is in a source docstring, not only in `docs/`: `Graded/Traverse.lean:35-38` — "the *precision* claim — that grade `g` is not padding, that no error kind admitted by the signature is actually unreachable — is exactly `foldGrade_cons_ne_nil`". `foldGrade_cons_ne_nil` says `foldGrade g xs = g` for `xs ≠ []`. It says nothing about reachability; `f := fun _ => .ok 0 : α → Graded {E.parse} Nat` satisfies it with `E.parse` unreachable. |
| 3 | Error kinds have no payloads | **Confirmed, and it contradicts the design doc** | `Graded/Carrier.lean:19-21`, `err : (e : Err) → e ∈ g → Graded g α`. `docs/design.md:44-45` states the C++ counterpart as "An instance holds **one** error value, whose type is in the set." The model holds the *type*, not the value. This is the one gap where the model is narrower than the design it exists to check. |
| 4 | `traverse` specialized, not a traversable abstraction | **Confirmed** | `Graded/Traverse.lean:106` and `Graded/Sufficient.lean:332` are both `List` × `Graded`. `Graded/Accum.lean` has **no traversal at all** — 22 declarations, none of them `traverse`. The accumulating carrier, whose entire reason to exist is collecting independent failures, is never traversed. |
| 5 | Generic grade algebra disconnected from carrier operations | **Confirmed, completely** | `grep -rl Pomonoid --include=*.lean` returns exactly two files: `Graded/Obligations.lean` and `Tests/Obligations.lean`. No carrier module imports `Obligations`. The abstraction and the model do not touch. |
| 6 | Canonical representation is not C++ type identity | **Confirmed** | `Graded/Canonical.lean:96-97`: "The Lean statement of \"`error_set<A,B>` and `error_set<B,A>` are the same type\"". It is not; it is an `Equiv` between two Lean representations of one grade. |
| 7 | The two morphism records do not share a complete bridge | **Confirmed, and the outline over-diagnoses it** | `GradedHom` (`Graded/Morphism.lean:222-233`) has `gmap_join`/`gmap_bot`/`hom_bind`/`hom_pure`. `GradedHomK` (`Graded/Sufficient.lean:915-922`) needs `gmap_mono`/`hom_bindK`/`hom_pureK`. `gmap_mono` is **already derived** — `GradedHom.gmap_mono`, `Graded/Sufficient.lean:1024`. See §3.1(d): the bridge needs exactly one new field, and it is not the one the outline emphasises. |
| 8 | Test policy not mechanically enforced | **Confirmed, quantified** | 203 `theorem` declarations, 194 distinct names. 56 of those names appear nowhere in `Tests/*.lean` or `Examples/*.lean`, not even in a comment. |
| 9 | Module boundaries hide dependency costs | **Confirmed** | `Graded/Sufficient.lean` is 1099 lines carrying `bindK`, `apK`, `traverseK`, `flattenK`, `Comp.apK`, `traverseCompK` and `GradedHomK`. `Graded/Canonical.lean` imports `Graded.Tuple` for `joinAll` alone. |

Nine for nine on substance. Two are mis-scoped (2 understates, 7
over-diagnoses); none is wrong.

---

## 2. What the outline gets right and undersells

**Problem 2 is the highest-value item in the document and it is buried
third from the top of a list, with no phase of its own.** A false claim
sitting in a source docstring in a repository whose entire product is
"claims that are checked" is a different kind of defect from an
abstraction that is narrower than it could be. It costs about twenty
minutes to fix. It should be first, alone, and shipped before anything
else is discussed.

**The `pureK`-as-derived argument is already satisfied and the outline
does not notice.** `Graded/Sufficient.lean:51` defines `pureK a` as
`fromEmpty a`, which is `widen (Grade.bot_le g) (emptyEquiv.symm a)` —
exactly the outline's prescription, already in the tree. Half of the
"operational interfaces" section describes the concrete layer that
`Graded/Sufficient.lean` already is: 57 laws, `0 of 57` statements
containing a `cast` (verified in `tmp/plan/MIGRATION-REVIEW.md` §1.1
against 38 of 146 at the union-graded layer). What is actually missing is
the *class* over abstract `G` and `M`, not the discipline.

**The `hom_widen` diagnosis is correct and provable today.** See §3.1(d).

---

## 3. Defects in the outline

### 3.1 Bugs in the proposed target design

**(a) Two `pure`s, and a `GradedFunctorK` diamond.** As written, both
`GradedMonadK` and `GradedApplicativeK` declare `pure` and both
`extends GradedFunctorK`. A carrier with both instances — which is
exactly `Graded`, the short-circuiting carrier — then has two `pure`
fields needing a coherence law, and two routes to `GradedFunctorK`. This
is precisely the objection the outline itself raises against a primitive
per-grade `pureK`, and precisely the diamond its own "Risks and controls"
section says to avoid. Fix: one `GradedPointedK` (or put `pure` on
`GradedFunctorK`), and have `GradedMonadK`/`GradedApplicativeK` take the
functor as an instance parameter rather than extend it.

**(b) `ErrorAdmission` is inert as specified.** The class relates `Kind`
to `G` and to `le`, and says nothing about any carrier. Nothing can be
proved from it about `M g α`. The missing field is the one that gives it
force: for the carrier's error constructor, `Admits k g` is the
admissibility side-condition — i.e. the class must be a parameter of the
carrier's formation rule, or must come with a law
`∀ {g α} (x : M g α) (k), emits x k → Admits k g`. As written it can be
instantiated and then never used.

**(c) `CompleteGrade`'s existential binds a variable it already has.**

```lean
forall k, k ∈ g -> exists (a : alpha) (payload : S.Payload k) (hk : k ∈ g), ...
```

`hk : k ∈ g` is already in scope as the hypothesis of the outer `∀`, and
`k ∈ g` is a `Prop` on a `Finset`, hence proof-irrelevant, so the
existential is vacuous. Drop it and use the hypothesis.

**(d) The `GradedHom → GradedHomK` bridge needs exactly one new field,
and the outline names two.** `GradedHom` already yields `gmap_mono`
(`Graded/Sufficient.lean:1024`). Adding one field

```lean
hom_widen : ∀ {g g' α} (h : g ⊆ g') (x : Graded g α),
    hom (widen h x) = widen (gmap_mono h) (hom x)
```

suffices, and the derivation is short: `bindK hg hh x f` is
`widen (join_le hg hh) (bind x f)` by `bind_eq_bindK`; push `hom` through
with `hom_widen`; rewrite the inside with `hom_bind`; discharge the
`cast (gmap_join g h)` with `widen_cast`. `hom_pureK` follows the same
way from `hom_pure`, `gmap_bot` and `widen_cast`. The outline's second
requirement — "one payload-independent mapping of error alternatives" —
is a genuine gap, but it is a *payload* requirement (Problem 3), not a
bridge requirement. Conflating them makes a one-field, one-afternoon fix
look like it depends on the largest phase in the plan. It does not, and
it should ship in the first week.

### 3.2 Factual errors about the current state

- **"Add CI"** (Phase 0, item 4). CI exists: `.github/workflows/ci.yml`,
  on push and PR, installs elan, fetches the Mathlib cache, runs
  `make all`. Only `make test-coverage` is missing.
- **The acceptance-command list silently drops `make letters`.**
  `make all` today is `verify nosorry letters laws`. The outline's
  replacement list is `verify nosorry laws test-coverage axioms cpp-probes`.
  Adopting it as written removes `scripts/check-letters.sh` from CI and
  regresses an enforced invariant.
- **`make axioms` is a good addition and is not a replacement for
  `nosorry`.** `nosorry` is a text grep and cannot see an axiom reached
  through a dependency; `#print axioms` cannot see a `sorry` in an
  unreferenced declaration. Keep both. The two prior reviews already ran
  `#print axioms` by hand on 25 declarations
  (`tmp/plan/INTEGRATION-REVIEW.md`, `tmp/plan/MIGRATION-REVIEW.md`), each
  reporting `[propext, Classical.choice, Quot.sound]` and nothing else —
  mechanising that is the right move and the expected output is known.

### 3.3 It reverses a documented decision without an amendment

`Graded/Obligations.lean`'s module docstring records `[obligation-layering]`
as a deliberate, argued choice: mixins `extends Pomonoid` (single
inheritance, one instance-search route), `IsCanonicalPomonoid` restating
both fields directly rather than extending both siblings, and
`foldG_le`/`joinAllG_perm` taking exactly one class so no two `Pomonoid G`
terms can disagree. The outline proposes `class IsPartialOrderGrade (G)
[PreorderedGradeMonoid G] : Prop` — parameterised `Prop` mixins — which
is the better idiom and does dissolve `IsCanonicalPomonoid`'s field
duplication, but it is a **reversal**, and `docs/RULES.md` says a change
of hypothesis shape is "a finding, not a licence: halt with an amendment".
The outline must carry that amendment explicitly, and must say what
happens to `IsCanonicalPomonoid` (my answer: delete it; with parameterised
mixins `[IsCommGrade G] [IsIdemGrade G]` *is* the bundle, and the C++
"canonical exact spelling" reading can be an abbreviation).

It also never mentions `blog/letters/`. Every completed step in this
project produced a dated, first-person letter, and `scripts/check-letters.sh`
binds letter slugs to checklist entries. `Pomonoid` appears in
`grade-obligations.org`, `obligation-layering.org` and `closing.org`, and
there is a letter whose slug *is* `grade-pomonoid`. **Those letters are
historical accounts and must not be retro-edited to use a name that did
not exist when they were written.** The rename gets a new letter saying
the old name was wrong; the slug stays.

### 3.4 The coverage mechanism is too blunt

A `-- TESTS:` marker per theorem plus a hand-reviewed JSON exemption file
means, on today's tree, **56 exemptions written by hand on day one** —
and inspecting the 56 shows why that is the wrong shape. They are almost
entirely `rfl` reduction lemmas: `foldGrade_nil`, `foldG_cons`,
`cast_ok`, `cast_err`, `ap_ok_ok`, `apK_err_left`, `traverseK_nil`,
`rename_ok`, `joinAll_cons`, and their kin. These are not untested; they
are the equations every `#guard` in the repository computes *through*.
Writing 56 prose justifications for them produces a file nobody reads and
teaches the next contributor that the exemption file is where theorems go
to be ignored.

Classify instead. Three classes, machine-assignable, one rule each:

| class | detection | rule |
|---|---|---|
| reduction | proof is `rfl`/`:= rfl`, statement is a computation rule | covered if its module's test file has at least one `#guard`/`decide` that reduces (already `docs/RULES.md`'s standing requirement) |
| law | has a `PROPERTY:` tag in `docs/laws.json`, or is cited by a C++ equation in `docs/probe-harness.md` | needs an `example` that *applies* it, meeting the fixture requirements below |
| counterexample / instance | statement is a `¬`, or the declaration is an `instance` | needs an `example` that evaluates the witness |

`docs/laws.json` already carries the tag data; `scripts/laws-inventory.py`
already parses every declaration. This is a companion pass over an
existing parse, not a new mechanism, and it produces a handful of
exemptions rather than 56.

Keep the outline's fixture requirements verbatim — distinct nonempty
grades for associativity, a nontrivial equality for morphism casts,
distinguishable kinds *and* payloads for both-error tests, zero/one/many
failures for accumulating traversal. Those are the actual content of the
proposal and cannot be mechanised; they are per-theorem judgement, and
they are worth the labour.

### 3.5 The payload phase is under-priced

`.err` appears **175 times** across `Graded/`, `Tests/` and `Examples/`,
concentrated in `Accum.lean` (22), `Sufficient.lean` (20), `Compose.lean`
(18) and `ComposeApp.lean` (14). Three costs the outline does not name:

- **`DecidableEq` breaks.** `Graded.instDecidableEq`
  (`Graded/Carrier.lean:66-79`) works because the membership proof is a
  `Prop` and two `err`s are equal iff their kinds are. With a dependent
  payload, `.err k p hk = .err k' p' hk'` needs `k = k'` *and* `HEq p p'`
  — a `Sigma` equality. Every `#guard` in the repository depends on this
  instance, and `docs/RULES.md` requires a computing `#guard` in every
  test file. A `[∀ k, DecidableEq (S.Payload k)]` instance and its `Repr`
  companion are deliverables, not details.
- **Universes move.** `Graded g α` is `Type u`-in-`Err`, `Type v`-in-`α`.
  `Sigma S.Payload` lands in `Type (max u v)`, so the accumulating
  carrier's error list changes universe while the short-circuiting one
  does not. `docs/RULES.md`'s "universe-polymorphic `Type u` for carriers"
  convention needs a revision, stated up front.
- **Equivalence is the wrong bridge.** The outline says "prove an
  equivalence to the current `Graded`" so that existing examples remain
  available. An `Equiv` does not carry 203 theorems across; each one has
  to be transported or re-proved. Prefer **definitional specialization**:
  define `ExpectedG` first, then `Graded` as its `Payload := fun _ =>
  PUnit` instance with `Graded.err e he := ExpectedG.err e ⟨⟩ he` as a
  smart constructor and a custom `@[induction_eliminator]`. Then the
  legacy theorems keep working with only pattern-syntax churn, and the
  unit-payload "equivalence" is `rfl` rather than a transport. Decide this
  before Phase 2 starts; it is the difference between one week and four.

### 3.6 Phase 5 is gated on an artifact outside this repository

There is no C++ in the tree. `docs/probe-harness.md` (317 lines) is
*generated* from `docs/laws.json` and states its own scope: "Nothing here
runs C++." `make cpp-probes` and "the C++ probes are green in CI" cannot
be a definition of done for this repository. Split it: the *reword* is
free and belongs in the first tranche; the probe corpus can be written and
committed as a standalone translation unit with no build wiring; "green in
CI" moves to the C++ repository's definition of done, not this one.

### 3.7 Omissions

- `Graded/Tuple.lean` (heterogeneous `HList` sequencing, 149 lines) has no
  sufficient-grade sibling — there is no `sequenceK` in
  `Graded/Sufficient.lean` — and the outline mentions `Tuple` only to
  extract `joinAll` out of it. What happens to heterogeneous sequencing
  under payloads and under the abstract classes is unaddressed.
- `Graded/Ungraded.lean` (288 lines, the fixed-grade baseline that shows
  which findings are *not* costs of grading — `INTEGRATION-REVIEW.md` §1.1
  leans on it) is never mentioned.
- `Graded/Compose.lean` and `Graded/ComposeApp.lean` (631 lines together)
  are covered by one bullet, "composed applicatives".
- **No kill criterion.** Phase 1 is a bet: that abstracting `G` and `M`
  buys more than it costs in elaboration time and readability. Bets need
  an exit. §5 supplies one.

---

## 4. The finding the outline misses

The outline proposes `IsPartialOrderGrade` as a mixin and correctly
observes that antisymmetry plus the least-upper-bound laws yields
idempotence. It does not notice that **on today's tree that mixin would
have no discriminating witness**: `⊆` on `Finset` is antisymmetric and
`≤` on `Nat` is antisymmetric, so both existing instances inhabit it, and
a class every instance satisfies proves nothing. The value of
`Graded/Obligations.lean` is entirely in the `Nat` counter-instance that
*fails* idempotence; an antisymmetry mixin without a counterpart is
decoration.

The witness exists, it is one screen of Lean, and it is the most
C++-relevant object in the whole proposal: **the un-canonicalized pack.**

```lean
-- grades as a raw, unsorted, un-deduplicated pack of error kinds:
-- exactly `error_set<Es...>` *before* the alias delegates to its
-- sorted detail carrier.
instance : Pomonoid (List Err) where
  join := (· ++ ·)
  bot  := []
  le   := fun g h => ∀ e ∈ g, e ∈ h
  ...
```

It satisfies every `Pomonoid` field. It satisfies `join_le` — so it is a
least-upper-bound grade, unlike `Nat`. And it fails antisymmetry:
`[A,A] ≤ [A]` and `[A] ≤ [A,A]`, but `[A,A] ≠ [A]`. Consequently
`join_comm` and `join_idem` both fail *as equalities* while holding as
order-equivalences.

That is the whole story of `error_set` canonicalization, as a
counter-instance:

- **Problem 1 and Problem 6 are one problem.** The raw pack is a
  preordered monoid; `Finset` is its poset quotient; `Canon` is a chosen
  normal form for that quotient. Commutativity and idempotence are not
  axioms the grade happens to have — they are what quotienting *buys*, and
  antisymmetry is exactly the property that turns the equivalence into an
  equality. `docs/design.md:2617-2625` already suspects the connection
  ("`join_le` plus antisymmetry *proves* `join_idem`"); the `List Err`
  instance is what makes it a demonstration instead of a remark.
- It closes `grade-join-strength` (OPEN since `[grade-obligations]`,
  reframed by `[obligation-layering]`, `docs/design.md:2216`) with a
  witness rather than at the type level only.
- It is directly legible to the C++ reader the letters are written for:
  the model now contains both the pack and the alias, and proves what the
  alias is for.

This is Tranche B below. It is small, and it is the best evidence-per-line
in the document.

---

## 5. The counter-plan

**Principle.** Order by evidence delivered per unit of churn, and gate.
Each tranche ends at a green `make all`, a committed letter, and a
regenerated `docs/laws.json`. No tranche starts before the previous one's
gate is met. Tranches A–D are independent of each other and of everything
downstream; E–G are a chain, each with an exit.

### Tranche A — truth in labelling (no new Lean content)

The repository currently asserts three things it has not proved. Remove
them. This tranche adds no definition and no theorem.

1. `Graded/Traverse.lean:35-38` — rewrite the "precision" paragraph.
   `foldGrade_cons_ne_nil` is annotation normalization: the *stated* grade
   of a nonempty traversal is `g` on the nose, independent of length. It
   is not a reachability claim, and the docstring must say which error
   kinds may be unreachable and that the model is silent on it.
2. `Graded/Canonical.lean:96-97` and the `#representation` anchor —
   `canonEquiv` is a representation theorem relating two Lean spellings of
   one grade. It is not C++ type identity, alias identity, mangling
   stability, or cross-TU normalization. State what `LinearOrder` buys and
   what it does not.
3. `Graded/Obligations.lean:17,95-96` — `Pomonoid`'s fields are a
   preorder. Correct the prose *now*; defer the rename to Tranche B where
   it is paid for by a real instance.
4. Sweep `docs/design.md` for the same three claims (51 `Pomonoid`
   mentions; the `#cpp-counterpart`, `#traverse`, `#representation`
   anchors).

Do **not** edit `blog/letters/*.org`. They are dated accounts.

**Gate:** `make all` green; `git diff` touches only docstrings, `docs/`,
and regenerated law files; no theorem statement changes; one letter,
`truth-in-labelling`.

### Tranche B — close `grade-join-strength` with a witness

1. Add the `List Err` pre-canonical pack instance from §4 to
   `Graded/Obligations.lean`, with `#guard`s showing `[A] ++ [A] ≠ [A]`
   and the two-way `le`.
2. Add `IsLubGrade` (field: `join_le`) and `IsPartialOrderGrade` (field:
   `le_antisymm`) as `Prop` mixins **parameterised** by `[Pomonoid G]`,
   not extending it. Carry the `docs/RULES.md` amendment reversing
   `[obligation-layering]`'s `extends` decision, with its reason: the
   parameterised form is what lets `List Err` inhabit `IsLubGrade` and not
   `IsPartialOrderGrade`, which the `extends` form cannot express without
   a diamond.
3. Prove `IsIdemGrade.ofLubOfAntisymm` as a **theorem, not an instance**
   (an instance would create a second route to `join_idem` for `Grade Err`,
   which already has it as a field).
4. Prove the preorder-only version: LUB alone gives
   `le (join a a) a ∧ le a (join a a)`, and `List Err` witnesses that this
   cannot be strengthened to equality.
5. Migrate `IsCommPomonoid`/`IsIdemPomonoid` to the parameterised form,
   delete `IsCanonicalPomonoid` (replaced by the conjunction of two
   mixins), and rename `Pomonoid` → `PreorderedGradeMonoid`. Mechanical:
   two `.lean` files, `docs/design.md`, regenerated law files. Letter
   slug `grade-pomonoid` is unchanged.
6. Update `docs/design.md#grade-join-strength` from OPEN to CLOSED, citing
   the witness.

**Gate:** `List Err` inhabits `PreorderedGradeMonoid` and `IsLubGrade` and
provably not `IsPartialOrderGrade`; `grade-join-strength` closed; no
operational theorem acquires a hypothesis it did not have.

### Tranche C — the two cheap missing theorems

1. **`Accum` traversal.** `Graded/Accum.lean` has no traversal, and
   collecting independent failures is the carrier's only reason to exist.
   Add `Accum.traverseK` at a nominated grade (matching
   `Graded/Sufficient.lean:332`'s shape), and prove: errors appear in
   source-list order; every failing position contributes; success is
   `List.map`; and `Accum.toGraded` (first error) commutes with it into
   `traverseK`. That last one is the payoff — `Accum.toGraded_grade'`
   (`Graded/Accum.lean:321`) already proves the projection is an
   unconditional applicative morphism, so the traversal commutation should
   fall out, and it is the interoperability guarantee
   `INTEGRATION-REVIEW.md` §1.2 tells the C++ side it has for free.
2. **Complete the morphism bridge.** Add `hom_widen` to `GradedHom`
   (§3.1(d)), prove `GradedHom.toGradedHomK`, and re-express `renameHomK`
   as its image of `renameHom`. Keep `constHomK_not_gmap_bot`
   (`Graded/Sufficient.lean:1088`) as the standing proof that the reverse
   conversion is unavailable.

Both are self-contained, need no abstraction, and each closes a gap the
outline defers behind its two largest phases.

**Gate:** accumulating traversal tested at zero, one, and multiple
failures with distinguishable kinds; `renameHomK` no longer defined
independently.

### Tranche D — coverage enforcement, classified

Implement §3.4: extend `scripts/laws-inventory.py` with a coverage pass
over its existing parse, three classes, exemptions in a reviewed JSON with
a reason field. Add `make test-coverage` and `make axioms` (`#print axioms`
over the `law`-class declarations, asserting the closure is a subset of
`{propext, Classical.choice, Quot.sound}`). Add both to `make all` —
**alongside `letters`, not replacing it** — and to `.github/workflows/ci.yml`,
which already runs `make all` and needs no other change. Add the
periodic cold `lake exe cache`-less dependency-resolution job the outline
asks for as a separate scheduled workflow, not on every push.

Then work the backlog to green: the fixture requirements are the labour,
and they are the point.

**Gate:** `make all` green including `test-coverage` and `axioms`;
exemption file under twelve entries, each with a reason a reviewer signed.

### Tranche E — abstract operational classes (**bet, with an exit**)

`PreorderedGradeMonoid` today is inhabited by four grades and consumed by
nothing (§1, Problem 5). Connect it.

1. `GradedFunctorK` carrying `map`, `widen`, **and `pure`** — one `pure`,
   not two (§3.1(a)).
2. `GradedMonadK` and `GradedApplicativeK` taking `[GradedFunctorK G M]`
   as an instance **parameter**, not `extends`.
3. Laws in separate `Lawful*` classes.
4. Instantiate for `Graded` and `Accum`; `Accum` gets applicative and
   **no** monad instance, with `Accum.notMonad`
   (`Graded/Accum.lean:235`) cited as the reason.
5. Derive `bind`/`ap` at the exact union from the two join inclusions;
   the four existing bridges (`bind_eq_bindK`, `ap_eq_apK`,
   `traverse_eq_traverseK`, `flatten_eq_flattenK`) become the
   compatibility statements.
6. `List.traverseGK` defined once over `GradedApplicativeK`; instantiate
   at `Graded`, `Accum`, and `Comp`; prove identity, composition,
   naturality and `map` fusion at the polymorphic layer, keeping shape
   preservation as a `List`-specific law.

**Exit criterion, checked at step 3 before any migration:** if the
abstract laws for `Graded` need more `simp` scaffolding than the concrete
ones they replace, or if elaboration of `Tests/` slows by more than
roughly a third, stop. Keep the classes as an additive layer that the
concrete development does not depend on, record the finding, and skip
Tranche G's re-pointing. That outcome is a *result* — "this abstraction
does not pay for itself at this size" is exactly the kind of thing this
repository exists to establish — not a failure.

**Gate:** generic law statements mention no `Finset`; no sufficient-grade
statement contains a `cast`; `Accum` has no monad instance; every existing
counterexample computes to the same value.

### Tranche F — payloads (largest; gated on E)

Decide the bridge **first** (§3.5): definitional specialization, not
`Equiv`. Then:

1. `ErrorSignature`; `ExpectedG` with the dependent payload; `Graded` as
   its `PUnit` specialization with a smart constructor and custom
   eliminator.
2. `DecidableEq` and `Repr` instances for `ExpectedG` given
   `[∀ k, DecidableEq (S.Payload k)]` — **before** anything else, because
   every `#guard` depends on them.
3. The `docs/RULES.md` universe amendment.
4. Payload-bearing accumulation over `Sigma S.Payload` with left-to-right
   order as a stated, tested contract (an unordered bag is a *separate*
   carrier if ever wanted).
5. Payload preservation under `map`, `widen`, `bindK`, `apK`.
6. `ErrorSignatureMap`, and the payload-independent error mapping the
   morphism interface has been missing (§3.1(d)'s second half, now paid
   for).
7. `CompleteGrade` — corrected per §3.1(c) — stated as an optional,
   generally-false side condition, proved to lift to traversal via
   singleton lists, and attached to **no** ordinary traversal law.
8. Port `Examples/Validation.lean` to parse locations / error codes /
   range bounds; keep the tag-only examples as compatibility tests.

**Gate:** unit-payload specialization recovers legacy results by `rfl`,
not by transport; `#guard`s still compute; many-to-one kind maps carry an
explicit payload conversion.

### Tranche G — modularize

The outline's twelve-module layout, with the current entry points kept as
re-export shims, and `joinAll` extracted so `Canonical` no longer imports
`Tuple`. Add `Graded/Traversable/Tuple.lean` for the heterogeneous
sequencing the outline forgot (§3.7). Nothing is deleted without a proved
bridge and green coverage.

**Gate:** importing `MonadK` does not transitively import traversal,
composition or morphisms; no public theorem disappears without an alias or
a documented migration; the law inventory distinguishes generic, concrete,
representation and C++-probe obligations.

### Deferred out of this repository

The C++ probe corpus. Write it — the outline's `static_assert` sketch is
right, and multi-TU plus mangled-name comparison is the correct shape —
commit it under `cpp/probes/` unwired from `make all`, and make "probes
green" the definition of done for the C++ implementation's repository.
The Lean side's obligation is discharged by Tranche A item 2: state the
boundary honestly and claim nothing the Lean does not prove.

### Execution

Tranches A–D are hand-sized: four to seven commits each, no design
uncertainty, and each is a single sitting. E–G are the shape this
repository's existing `tmp/plan/` machinery was built for — one step file
per numbered item, one cleared worker each, `handoff-<slug>.md` between
them — and should be decomposed that way when Tranche D's gate is met,
not before. Each completed step owes a letter under `blog/letters/`
per `docs/RULES.md`, and `scripts/check-letters.sh` will enforce it.

---

## 6. Revised definition of done

Unchanged from the outline, minus the two items this repository cannot
own, plus the one it should:

- the grade algebra uses accurate preorder / partial-order terminology,
  **and the distinction is witnessed by an instance that separates them**;
- `grade-join-strength` is CLOSED, with the witness named;
- no theorem or docstring confuses an annotation with behavioural
  reachability;
- the primary expected-style carrier stores typed error payloads, and the
  tag-only model is its `PUnit` specialization definitionally;
- monad and applicative laws are proved over abstract sufficient-grade
  interfaces **or** the exit criterion of Tranche E has been invoked and
  the finding recorded;
- list traversal is polymorphic over graded applicatives and is exercised
  by both the short-circuiting and the accumulating instance;
- morphisms commute with widening and carry errors through an explicit
  signature map;
- representation equivalence and C++ type identity are stated in their
  proper layers, and the Lean side claims neither ABI nor type identity;
- every inventoried theorem is covered under its class, or exempt with a
  signed reason;
- `make verify nosorry letters laws test-coverage axioms` green in CI.

The C++ probe corpus exists and is unwired; "probes green" belongs to the
C++ repository.
