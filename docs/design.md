# Design — Lean model of graded Transpose

## toolchain

`lean-toolchain`: `leanprover/lean4:v4.34.0-rc2`, taken verbatim from the
Mathlib-recommended bootstrap (`lake +leanprover-community/mathlib4:lean-toolchain
new transpose_lean math`); not hand-picked.

Mathlib pin (from `lake-manifest.json`, `require` entry `mathlib`,
`inputRev = "v4.34.0-rc2"`): commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

Cache command: `lake exe cache get` (the `math` template also runs this as
part of `lake new`, so the very first `lake build` in this repo already had
the Mathlib oleans in place).

Build times (`make verify`, i.e. `lake build`), measured on this step:

- Cold (`.lake/build` for the project's own targets removed, Mathlib cache
  from `lake exe cache get` still present): see `tmp/plan/metrics.jsonl`,
  row `verify-floor`, field `note`.
- Warm (nothing changed, cache present): see the same row.

> **Provisional.** The exact wall-clock numbers depend on this machine and
> this network path to the Mathlib cache blob store. Revisit if a later
> step's CI run reports a materially different floor.

### Lint configuration

The Mathlib `math` template enables `weak.linter.mathlibStandardSet`, whose
rules assume files destined for Mathlib itself. Three are turned off in
`lakefile.toml` because they contradict this project rather than describe
it: `style.header` (wants a Mathlib copyright block in every file),
`hashCommand` (forbids `#guard`/`#eval`, which `docs/RULES.md` *requires* in
every test file so that definitions are known to compute and not merely
typecheck), and `dupNamespace` (flags `Graded.Graded`, the name this plan
specifies). The rest of the set is left on. A green build is expected to be
a silent build; a warning means someone introduced one.

## cpp-counterpart

The grade is `error_set<Es...>`: a set of error *types*, ordered by
inclusion, joined by union; ∅ is the unit. It is a nominal type, not a bare
pack. Canonicalization is *type-level identity*: `error_set<A,B>` and
`error_set<B,A>` are the same type, via a public alias delegating to a
sorted detail carrier. An instance holds **one** error value, whose type is
in the set; value equality is variant-style.

The carrier at grade `Es` is `expected<T, error_set<Es...>>`; at grade ∅ it
is **bare `T`** (decided for client-API risk reasons), so ∅-grade is a
different C++ type from `expected<T, error_set<>>`.

Subsumption `Es ⊆ Es'` is an implicit conversion of the carrier.

`bind` produces the *union* grade; `pure` produces grade ∅.

The applicative typeclass instance for a monad is stated to be identical to
(not merely derivable from) the monad instance.

`traverse` is shape-preserving over ranges and over tuples.

Typeclass instances are duck-typed "gadgets" needing only a couple of
functions; no law checking exists in the C++ machinery; std types are the
intended test probes if a law harness is added.

Only `error_set` is intended as a grade for now; the design should not make
it the *only possible* grade.

## grade

`Graded.Grade Err := Finset Err`, for `[DecidableEq Err]`: a grade is a
finite set of error kinds. `Err` stands in for the universe of C++ error
types (see [cpp-counterpart](#cpp-counterpart)); `DecidableEq` is what lets
Lean form a `Finset` over it at all — the closest thing to "these are
distinct types" that Lean needs spelled out, where C++ gets it for free
from nominal typing.

`bot := ∅`, `join g h := g ∪ h`; the order is `⊆` (Finset's own
`PartialOrder`), read as "subset" rather than translated to `≤`, so a C++
reader sees the relation they already know.

Every pomonoid property `Graded.Grade.join`/`bot`/`⊆` has is a *separately
named* lemma in `Graded/Grade.lean`, each proved by one Mathlib `Finset`
lemma, never re-derived inline, so a later step can cite the property by
name:

- `join_assoc`, `join_comm`, `join_idem`
- `bot_join`, `join_bot`
- `le_join_left`, `le_join_right`, `join_le`, `join_mono`
- `le_refl'`, `le_trans'`, `bot_le`
- `join_eq_right_of_le`

Five of these carry a `/-- PROPERTY: ... -/` docstring tag —
`associative`, `commutative`, `idempotent`, `unit` (on both `bot_join` and
`join_bot`), `order` (on both `le_refl'` and `le_trans'`) — which is what
[oracle-export](../tmp/plan/step-oracle-export.md) greps to find which laws
depend on which property.

> **Provisional.** No Mathlib lattice or ordered-monoid instance is
> *declared* for `Grade`, so that this module's named lemmas stay the
> entry points a grep can find.
>
> **Corrected 2026-09-08, after the run.** The original wording said an
> instance "would let `simp` reach for these properties invisibly", as
> though declaring none withheld them. It does not: `Grade` is an
> `abbrev` for `Finset`, so `Finset`'s own instances apply through it.
> Verified — `#synth SemilatticeSup (Grade E)`, `Lattice (Grade E)` and
> `OrderBot (Grade E)` all resolve (to `Finset.instLattice` and friends),
> and `example (g h : Grade E) : Grade.join g h = Grade.join h g := by
> unfold Grade.join; exact sup_comm ..` compiles. Mathlib's lattice API
> was available the whole time.
>
> What the decision did secure is narrower and did hold: every property
> of the grade has a *named* lemma here, and every proof in the model
> cites one rather than reaching for the Mathlib fact — confirmed by
> [oracle-export]'s generated table, where `Finset.union_*` appears only
> in this module. That was worker discipline, not a property of the
> type. A future run wanting the guarantee rather than the convention
> would need `Grade` to be a `def` or a one-field structure, which would
> cost instance resolution everywhere. Revisit only if a proof is
> otherwise long enough to be worth that.

## carrier

`Graded.Graded (g : Grade Err) (α : Type v)` (in `Graded/Carrier.lean`): an
`ok` holding a value of `α`, or an `err` holding one error value together
with a proof of its membership in `g`. Models `expected<T,
error_set<Es...>>` ([cpp-counterpart](#cpp-counterpart)); the membership
proof is what stands in for "one error whose *type* is in the set."

`map : (α → β) → Graded g α → Graded g β`, with laws `map_id`, `map_comp`.
The grade does not appear in `map`'s type — functors are oblivious to
grading, true by construction, not by proof.

`emptyEquiv : Graded (Grade.bot : Grade Err) α ≃ α` settles the ∅-grade
question honestly: `Graded ∅ α` is a different *type* from `α` (its `err`
constructor exists, merely uninhabited — `Finset.notMem_empty` closes that
case), but is *isomorphic* to it, and the isomorphism is natural in `map`
(`map_emptyEquiv`). That naturality is what "bare `T` is safe at grade ∅"
means: every operation on the two representations agrees, not just their
storage. C++'s implicit conversion at grade ∅ asserts the same
identification without proof.

`cast (h : g = g') : Graded g α → Graded g' α`, with `cast_rfl`,
`cast_cast`, lets later steps state laws "modulo grade equalities."

`DecidableEq (Graded g α)` (given `DecidableEq α`, `DecidableEq Err`): the
membership proof is a `Prop`, hence proof-irrelevant, so two `err` values
compare equal exactly when their error values do — mirroring how C++
variant equality never has to look at "how" the alternative's admissibility
was established, because that fact is compile-time and already erased.

> **Provisional.** Laws are stated with exact union grades and `cast`,
> mirroring C++ where `bind` computes the union type. The alternative —
> `bind` at any sufficient grade `k` with `g ∪ h ⊆ k`, absorbing
> subsumption — would remove every `cast`. Revisit if [monad-laws] or
> [traverse-list] finds the casts dominate the proofs.
>
> **[monad-laws] verdict:** tolerable, not dominating. Three generic
> transport lemmas (`cast_ok`, `cast_err`, `cast_widen`), each proved by
> `subst e; rfl`, absorbed every `cast` the five monad laws produced; see
> [#monad](#monad) for the detail. Standing at the time, revisited below.
>
> **Integration review, 2026-09-08:** the burden had outgrown this
> verdict once the composite layers were counted — 39 of 146 theorems
> (26%) carry a `cast`, `Comp.ap_interchange` carries six in one
> statement, and `GradedHom`'s *fields* are cast-quantified.
>
> **[sufficient-grade-bind] verdict:** the alternative recorded above was
> a trap read literally — replacing `bind` with a caller-nominated grade
> models a design P3200 does not have, since the C++ `bind` genuinely
> computes the union. The actual fix is not replacement: `bindK` (in
> `Graded/Sufficient.lean`) exists *beside* `bind`, at any grade `k` with
> `g ⊆ k` and `h ⊆ k` supplied by the caller, and `bind_eq_bindK` proves
> the two are the same operation at `k := Grade.join g h`. The three
> monad laws restate with no `cast` at all, shorter than their
> union-graded counterparts (13 proof lines for `bindK_assoc` against 21
> for `bind_assoc`), and the two `⊆` proofs a call site threads are free
> — `bindK_irrel` is `rfl`. See [#monad](#monad)'s "The sufficient-grade
> layer" for the measurement table. Verdict: worth extending to the
> applicative layer; [sufficient-grade-applicative] is what tests it
> against the higher cast density there, and against the one open
> question this step's evidence could not reach — whether an `ap_flip`
> analogue needs `join_comm` the way `ap_flip` itself does.

The first consumer, `Examples/Validation.lean`: `parseNat : String →
Graded {E.parse} Nat` and `checkRange : Nat → Graded {E.range} Nat`,
composed by hand (`match`, no `bind` yet) into `validate : String →
Graded {E.parse, E.range} Nat` — the union grade and each `err`'s
membership proof assembled explicitly at the call site. Marked
`REPLACED-BY: bind` at its definition; [monad-laws] replaces this
composition.

## subsumption

`widen (h : g ⊆ g') : Graded g α → Graded g' α` (in `Graded/Widen.lean`):
the order half of the pomonoid made computational — an `ok` passes through
untouched, an `err`'s membership proof is carried along `h`. Models the
C++ implicit conversion `expected<T, error_set<Es...>> → expected<T,
error_set<Es'...>>` for `Es ⊆ Es'` ([cpp-counterpart](#cpp-counterpart)).

Four laws, each citing the [grade](#grade) lemma it needs:

- `widen_refl` (`Grade.le_refl'`): widening along the reflexive inclusion
  is the identity.
- `widen_widen` (`Grade.le_trans'`): widening twice agrees with widening
  once along the composite inclusion — the conversion path's endpoints
  determine the result, not the path.
- `widen_map`: naturality — mapping before or after widening agrees. No
  named [grade](#grade) lemma is needed; this is a property of `widen`
  and `map` alone.
- `widen_irrel`: proof irrelevance — any two proofs of `g ⊆ g'` widen a
  given value identically. Provable by `rfl`, because `⊆` on a `Finset`
  is a `Prop` and Lean's definitional equality already erases proof
  content; stating it as a theorem is what turns "the conversion path
  doesn't matter" from a convention C++ relies on into something Lean
  checks rather than assumes.

`widen_cast (e : g = g') (h : g' ⊆ g'') : widen h (cast e x) = widen (e ▸
h) x` settles the interaction between the two ways of changing a grade:
proving `⊆` (`widen`) and proving `=` (`cast`). It followed from `subst e;
rfl` on the first attempt — no `grind` loop was needed, contrary to this
step's own prediction that it would be fiddly.

Together these four laws (plus `widen_map`) say: subsumption is a
*functor* from the poset `(Grade, ⊆)` to endofunctors — the C++
conversion sequence is required to satisfy this and does, by these
theorems.

`fromEmpty : α → Graded g α := widen Grade.bot_le ∘ emptyEquiv.symm`
(citing `Grade.bot_le`) makes the bare-`T` handoff — "you can pass a bare
`T` where a graded value is expected" — a proved composite: go through
the ∅-collapse ([carrier](#carrier)'s `emptyEquiv`), then widen along
`∅ ⊆ g`. `fromEmpty_eq_ok : fromEmpty a = .ok a` is `rfl`.

`Examples/Validation.lean` gains a third stage, `logIt : Nat → Graded
{E.io} Unit`, and a `#guard` widening `parseNat`'s failure from grade
`{E.parse}` into `{E.parse, E.range, E.io}` and comparing it, via
`decide`, to the same failure constructed directly at that grade.

## monad

`Graded.pure (a : α) : Graded (Grade.bot : Grade Err) α := .ok a` and
`Graded.bind (x : Graded g α) (f : α → Graded h β) : Graded (Grade.join g
h) β` (in `Graded/Monad.lean`) model C++ `and_then`: the result grade is
the *union* of the input's grade and the continuation's. `bind` needs only
the order half of the pomonoid — `Grade.le_join_right` to widen the
continuation's result up to the union on the success path,
`Grade.le_join_left` to inject the input's own error on the failure path
— neither branch needs `join_comm`; the two sides of the union are kept
apart by which one-sided inclusion lemma reaches them, not by commuting
anything.

Five theorems, each citing the [grade](#grade) property it needs:

- `bind_pure_left` (unit, `bot_join`): `pure` on the left of `bind` is the
  continuation, up to `∅ ∪ h = h`.
- `bind_pure_right` (unit, `join_bot`): `pure` on the right is the
  original value, up to `g ∪ ∅ = g`.
- `bind_assoc` (associative, `join_assoc`): `bind` re-associates up to
  `(g ∪ h) ∪ j = g ∪ (h ∪ j)`.
- `bind_map` (unit, `join_bot`): `bind x (pure ∘ f) = map f x` up to
  `g ∪ ∅ = g` — the functor is the monad's functor.
- `bind_widen` (order, `join_mono` + `le_refl'`): subsumption commutes
  with `bind`; no `cast` at all, since widening produces an *inclusion*,
  not an equation, between the two sides' grades.

**Cast direction.** Every law with a `cast` states it as `cast
(Grade.<lemma> …) (<the compound bind/join expression>) = <the simpler
expression>`, always applying the pomonoid lemma in the direction it is
already stated in `Graded/Grade.lean` — never `.symm`. Concretely: `cast`
is applied to whichever side's grade is literally the `join`-expression
the named lemma's left-hand side matches (`Grade.join Grade.bot h`,
`Grade.join g Grade.bot`, `Grade.join (Grade.join g h) j`), transporting
it down to the grade the lemma's right-hand side names. This was a
free choice — the reverse direction (cast the simpler side up, with
`.symm`) typechecks equally well — but this one reads as "the messier
expression collapses to the tidy one," which matched every proof's
natural shape and meant no `.symm` was ever needed, at the law
statements or at their use sites in the tests.

**Verdict on the `cast` decision ([carrier](#carrier)):** tolerable, not
dominating, as far as [monad-laws] alone could tell. **Superseded by
[sufficient-grade-bind], below and at [carrier](#carrier): the
integration review found the burden had outgrown this verdict once the
composite layers (`Comp`, `GradedHom`) were counted.**

### The sufficient-grade layer

`Graded/Sufficient.lean` adds `bindK` beside `bind`, not instead of it.
Where `bind x f : Graded (Grade.join g h) β` *computes* the result grade,
`bindK (hg : g ⊆ k) (hh : h ⊆ k) (x : Graded g α) (f : α → Graded h β) :
Graded k β` takes a grade `k` merely *sufficient* to hold both — supplied
by the caller, via two inclusion proofs, rather than derived. `ok` hands
its payload to `f` and widens up to `k` along `hh`; `err` carries its
membership proof along `hg`. `pureK := fromEmpty` (reused, not
redefined) is `pure` at any grade directly.

Because `k` is never *equated* to another expression for the same grade
— there is nothing here shaped like `Grade.join Grade.bot h = h`, only a
hypothesis `Grade.bot ⊆ k` supplied once — the three monad laws restate
with **no `cast` anywhere**:

```lean
theorem bindK_pure_left (hh : h ⊆ k) (a : α) (f : α → Graded h β) :
    bindK (Grade.bot_le k) hh (pure a) f = widen hh (f a) := rfl

theorem bindK_assoc (hg : g ⊆ k) (hh : h ⊆ k) (hj : j ⊆ k)
    (x : Graded g α) (f : α → Graded h β) (kk : β → Graded j γ) :
    bindK (Grade.le_refl' k) hj (bindK hg hh x f) kk =
      bindK hg (Grade.le_refl' k) x (fun a => bindK hh hj (f a) kk) := by
  ...
```

`bind_eq_bindK` (tagged `BRIDGE`) is what keeps this a second view of the
same operation rather than a different design: instantiating `k` at the
exact union `Grade.join g h`, along the same two inclusions `bind` itself
already uses (`Grade.le_join_left`/`Grade.le_join_right`), recovers
`bind` — `rfl` in both constructor cases, exactly as verified before
planning this step.

**The property shift.** Every cast-free law cites an *order* lemma
(`Grade.bot_le`, `Grade.le_refl'`) where its union-graded counterpart
cited a *unit* or *associativity* lemma (`Grade.bot_join`,
`Grade.join_bot`, `Grade.join_assoc`) — confirmed by
`scripts/laws-inventory.py`'s own mention scan, not asserted. The grade
arithmetic that used to be an equation to transport across is now
subsumption: proving `g ⊆ k` rather than computing `g ∪ h` and proving it
equals something else.

**`bindK_irrel`** (`bindK hg hh x f = bindK hg' hh' x f`, for any two
proofs `hg, hg'` and `hh, hh'`) is `rfl` — which proof of `g ⊆ k`
justifies the call does not matter, and Lean confirms it definitionally
rather than by an argument about `Subsingleton`. This is the load-bearing
fact for the whole design: it is what makes the two inclusion proofs a
call site threads *free*, in the sense that no later reasoning has to
track which specific proof term was used.

**The measurement**, for the three monad laws only:

| law | casts in statement (before → after) | proof lines (before → after) |
|---|---|---|
| `bind_pure_left` → `bindK_pure_left` | 1 → 0 | 3 → 1 (`rfl`) |
| `bind_pure_right` → `bindK_pure_right` | 1 → 0 | 9 → 3 |
| `bind_assoc` → `bindK_assoc` | 1 → 0 | 21 → 13 |

What a call site pays: `bind x f` threads nothing — the result grade is
computed. `bindK hg hh x f` threads two `⊆` proofs. At a concrete grade
(`Examples.Validation.validateK`) both close with `by decide`; at an
abstract grade they are ordinary hypotheses, the same shape `bindK_assoc`
itself already carries for `hg`/`hh`/`hj`.

**The same measurement, extended to the applicative and composite layers
by [sufficient-grade-applicative]** (proof-line counts by
`scripts/laws-inventory.py`'s own chunker, statement text only for casts):

| law | casts in statement (before → after) | proof lines (before → after) |
|---|---|---|
| `ap_pure_id` → `apK_pure_id` | 1 → 0 | 5 → 5 (case split, no cast to discharge) |
| `ap_pure_pure` → `apK_pure_pure` | 1 → 0 | 6 → 4 (`rfl`) |
| `ap_interchange` → `apK_interchange` | 2 → 0 | 10 → 6 |
| `ap_comp` → `apK_comp` | 1 → 0 | 23 → 16 |
| `ap_flip` → `apK_flip` | 1 (`Grade.join_comm`) → 0 | — (new law, no union-graded proof-line baseline to compare against) |
| `Comp.ap_interchange` → `Comp.apK_interchange` | 6 → 0 | 19 → 10 |

**Verdict: worth extending to the applicative layer
([sufficient-grade-applicative]).** On every axis this step measured, the
sufficient-grade layer was strictly cheaper for `bind`: no casts, shorter
proofs, and the threaded obligations are free by `bindK_irrel`.
`Graded.Monad` had the worst cast ratio of any module (7/8); the
applicative layer's worst offenders (`Comp.ap_interchange` at six casts
in one statement, `GradedHom`'s cast-quantified fields) have more casts
to remove, not fewer, and `⊆`-proof-irrelevance is a generic fact about
`Finset`, not something specific to `bind` that might fail to
generalize. The one thing this step did *not* test: `ap_flip` needs
`Grade.join_comm` to compare `join g h` against `join h g`, and nothing
in `bindK` compares two different joins at all, because `bindK` never
computes a join in the first place. Whether an `apK`/`apFlippedK` pair
still needs commutativity, or whether working at a common `k` makes the
comparison vanish along with the cast, is a genuinely open question this
step's evidence cannot answer — that is exactly the finding
[sufficient-grade-applicative] has to make on its own.

**[sufficient-grade-applicative]'s answer: no, `apK_flip` needs no
`Grade.join_comm`, and the "third obligation" question resolved even
more sharply than predicted.** `apK`/`map2K` are built through `bindK`
exactly as `bind_eq_bindK`'s story predicted, with `pureK` (already
established to be `pure` widened to any grade directly, not pinned to
`Grade.bot`) used in place of `pure` — so `apK`'s intermediate step lands
at `k` immediately, via `Grade.le_refl' k`, and never introduces a `∅` to
collapse. The step's own predicted "third obligation" (one hypothesis per
input, plus one for `pure`'s own grade) does not merely come out free by
`bindK_irrel`-style proof irrelevance the way the two threaded `⊆` proofs
do — it never appears in `apK`'s signature at all: `apK` takes exactly
two hypotheses (`hg : g ⊆ k`, `hh : h ⊆ k`), the same count `bindK` has,
because `pureK` needs no inclusion proof of its own to be a value at `k`.
All four applicative laws (`apK_pure_id`, `apK_pure_pure`,
`apK_interchange`, `apK_comp`) state and prove cast-free, and every one
mentions only `Grade.le_refl'` — never a unit or associativity lemma, the
same "order replaces unit/associative" pattern [sufficient-grade-bind]
found for `bindK`'s three laws, now confirmed at the applicative layer
too.

## applicative

`Graded.ap (f : Graded g (α → β)) (x : Graded h α) : Graded (Grade.join g h)
β` (in `Graded/Applicative.lean`) is derived from `bind`/`pure` — not given
its own primitive definition — checking the C++ claim
([cpp-counterpart](#cpp-counterpart)) that the applicative instance for a
monad *is* the monad instance. `ap` sequences its two arguments through
`bind` in a fixed order, function first: `bind f (fun f' => bind x (fun a
=> pure (f' a)))`, cast once through `Grade.join_bot` to collapse the inner
`h ∪ ∅`. `apFlipped` sequences the other way (argument first) and lands at
`Grade.join h g` — the same two grades, joined in the other order.
`map2 (k : α → β → γ) : Graded g α → Graded h β → Graded (join g h) γ :=
ap (map k x) y` combines two independently-graded computations.
`seqLeft`/`seqRight` are omitted: nothing in this step's four laws or its
consumer needed them, and adding them speculatively would be exactly the
kind of unrequested API this plan avoids.

**Property table** — every one of the four applicative laws needs only
*unit* and/or *associativity*, never `join_comm`, confirming this step's
own prediction:

| law | property | note |
|---|---|---|
| `ap_pure_id` | unit (`bot_join`) | identity |
| `ap_pure_pure` | unit (`bot_join`, `∅ ∪ ∅ = ∅`) | homomorphism |
| `ap_interchange` | unit (`join_bot` *and* `bot_join`, separately) | interchange |
| `ap_comp` | unit (`bot_join`) + associative (`join_assoc`) | composition, the heaviest proof |

**`ap_interchange` finding.** The step brief predicted this law "needs
`join_comm`" then immediately doubted it ("`g ∪ ∅` vs `∅ ∪ g` are both `g`
by the unit laws alone"). The doubt was right: stated with **two** casts —
`cast (Grade.join_bot g) (ap u (pure a)) = cast (Grade.bot_join g) (ap
(pure (fun f => f a)) u)`, both sides landing at the same tidy grade `g` —
the law needs only the two unit lemmas, each in its own stated direction,
no `.symm` and no `Grade.join_comm`. A single-cast phrasing (cast one
side directly to the other's grade, `join g ∅` vs `∅ ∪ g`) would need
`join_comm` instead; the two-cast phrasing is the weaker-hypothesis proof
and is what's implemented.

**`join_comm` — where it is needed, and only there.** `ap_flip : ap f x =
cast (Grade.join_comm h g) (apFlipped f x)` is the one place `join_comm`
appears in the module. It is needed *by construction*: `ap`'s grade is
`Grade.join g h`, `apFlipped`'s is `Grade.join h g` — the same union with
its arguments the other way around — and relating them at all is exactly
what commutativity states, independent of any value-level question.

**The value-side finding — this is the substance of the C++ "identical"
claim.** `ap_flip` as a *value* equation is only provable under a
hypothesis: `(∃ f', f = .ok f') ∨ (∃ a, x = .ok a)` — at most one side is
an error. `Tests/Applicative.lean` gives the counterexample the step asked
for: `bothErrF : Graded {E.parse} (Nat → Nat) := .err E.parse _` and
`bothErrX : Graded {E.range} Nat := .err E.range _`. Both `ap bothErrF
bothErrX` and `apFlipped bothErrF bothErrX` land at the *same* grade
(`{E.parse, E.range}`, via `Grade.join_comm`) but disagree on the *value*:
`ap` (which sequences `f` first, matching `bind`'s own order) reports
`E.parse`; `apFlipped` (argument first) reports `E.range`. Whichever side
runs first is the error a caller sees. This is exactly the gap in the C++
claim: "the applicative instance is identical to the monad instance" is
true of the *grade* unconditionally, and true of the *value* only when at
most one side can fail — a condition the C++ design text never states,
because with a non-commutative grade the two orderings are observably
different operations.

The consumer, `Examples/Validation.lean`: `sumTwo (s1 s2 : String) :
Graded {E.parse} Nat := map2 (· + ·) (parseNat s1) (parseNat s2)` combines
two independent (non-`bind`-threaded) validations. Because both stages
share the error kind `E.parse`, `sumTwo`'s own `#guard`s can show
short-circuiting (either failure fails the whole) but not *which* side
failed — that distinction needs two different error kinds, which is what
`Tests/Applicative.lean`'s cross-grade counterexample is for.

### The sufficient-grade layer

`Graded/Sufficient.lean` extends [sufficient-grade-bind]'s `bindK` layer
to the applicative: `apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β))
(x : Graded h α) : Graded k β`, built through `bindK` exactly as `ap` is
built through `bind`, with `pureK` (`= fromEmpty`, already `pure` widened
to any grade) standing in for `pure`. Because `pureK`'s target grade is
`k` directly, `apK`'s two `bindK` calls both land at `k` via
`Grade.le_refl' k`, and there is no `∅` anywhere in the definition for the
`Grade.join_bot` cast `ap` pays to collapse. `map2K` is `apK` after `map`,
exactly as `map2` is `ap` after `map`. `apFlippedK` is the other
sequencing order, at the *same* `k` rather than a second, differently-
joined grade — the shape `ap_flip`'s finding below needed.

**The "third obligation" resolved more sharply than predicted.** The step
that authorized this one predicted `apK` would need three threaded
hypotheses where `bindK` needs two (one per input, plus one for `pure`'s
own grade), free at worst by the same proof-irrelevance argument
`bindK_irrel` established. It does not merely come out free: it is
**absent from the signature**. `apK` takes exactly `hg : g ⊆ k` and
`hh : h ⊆ k` — two hypotheses, the same count as `bindK` — because
`pureK` needs no inclusion proof of its own to be a value at `k`.

**The four applicative laws, cast-free**, every one citing only
`Grade.le_refl'`:

| law | property | note |
|---|---|---|
| `apK_pure_id` | order (`le_refl'`) | identity |
| `apK_pure_pure` | order (`le_refl'`) | homomorphism, `rfl` |
| `apK_interchange` | order (`le_refl'`) | interchange |
| `apK_comp` | order (`le_refl'`) | composition |

Where the union-graded laws needed *unit* (`bot_join`/`join_bot`) and, for
`ap_comp`, *associativity* (`join_assoc`) as well, the sufficient-grade
versions need nothing beyond the order hypotheses already threaded
through `apK`'s own signature — the same "order replaces unit/associative"
shift [sufficient-grade-bind] found for `bindK`'s three laws, confirmed
here too. Every one of the four proofs closes by `cases` down to `rfl`;
none cites a named `Grade` lemma inside its tactic block.

**`apK_flip`: the finding this step exists to make.** `ap_flip` needs
`Grade.join_comm` *by construction*: it compares `ap`'s grade `Grade.join
g h` against `apFlipped`'s `Grade.join h g` — two different expressions
for the same grade, and relating them at all is what commutativity says.
At a common sufficient grade `k`, `apK` and `apFlippedK` both already
land in `Graded k β`: there is no second expression for the same grade to
compare, so `apK_flip (hg : g ⊆ k) (hh : h ⊆ k) (f) (x) (honeok : (∃ f',
f = .ok f') ∨ (∃ a, x = .ok a)) : apK hg hh f x = apFlippedK hg hh f x`
states and proves with **no `Grade.join_comm`, and no property at all** —
the same one-sided condition `ap_flip` needs on the *value* survives
unchanged (both sides still disagree, at the *same* grade now, when both
inputs fail — `apK` keeps the function's error, `apFlippedK` keeps the
argument's), but the grade-level question `join_comm` answers for `ap`
never arises for `apK` in the first place.

**What this revises in [grade-obligations](#obligations).** That step's
three-layer account attributes commutativity's necessity to the
applicative's order-independence: `ap` and `apFlipped` combine the same
two values in the other order, and matching grades needs `join_comm`.
`apK_flip` shows this is not quite right. The applicative structure
itself — sequence a function and an argument through `bindK`, either
order — needs no commutativity at all, at any sufficient grade, including
the exact union (`ap_eq_apK`, below, recovers `ap` at `k = Grade.join g
h`). Commutativity was a cost of *computing the grade exactly as the
union `Grade.join g h`* and then insisting that the flipped
computation, `Grade.join h g`, be recognized as the same grade — a cost
of canonicalization, not of order-independence as a requirement on the
applicative. A design that tracked "a grade sufficient to cover both
inputs" rather than "the exact union" would never have needed
`join_comm` for this, at any layer.

`ap_eq_apK` (tagged `BRIDGE`) instantiates `apK` at the exact union
`Grade.join g h`, along the same two inclusions `ap` itself uses
(`Grade.le_join_left`/`Grade.le_join_right`), and recovers `ap` — the
applicative mirror of `bind_eq_bindK`, proved the same way (case split on
`f`/`x`, citing each side's own `ok`/`err` reduction lemma).

**The composite: `Comp.apK`, at a sufficient grade *pair*.** `Comp g h α`
([#compose](#compose)) already generalises over any two grades, so no
second nested carrier was needed — "sufficient" here is supplying `Comp`'s
own two indices as caller-chosen bounds `(k1, k2)` rather than the
componentwise joins `Comp.ap` computes. `Comp.apK` is built through
`map2K`/`apK` exactly as `Comp.ap` is built through
`Graded.map2`/`Graded.ap`: outer combine at `k1`, with the *inner* `apK`
(at `k2`) threaded through as the combining function. **The headline
measurement**: `Comp.ap_interchange` carries six casts in its statement
(two `Comp.castGH` calls, each bundling two `Graded.cast`s, driven by
`Grade.join_bot`/`Grade.bot_join` in each of the two components
separately); `Comp.apK_interchange`, at a common sufficient grade pair,
has **zero** — both sides already land in `Comp k1 k2 β`, so there is
nothing to `Comp.castGH`. Unlike `Comp.ap_interchange` (which cites
`Graded.ap_interchange` explicitly in its `ok` branch), the fully
case-split proof of `Comp.apK_interchange` closes by `rfl` alone: there is
no property left to cite, at either layer.

The consumer, `Examples/Validation.lean`: `sumTwoK`, `sumTwo`'s two
independent validations spelled through `map2K` at the literal grade
`{E.parse}` (which happens to equal the computed join, `Grade.join_idem`)
instead of `map2`'s computed union — `#guard`ed to render identically to
`sumTwo` on every input, the applicative mirror of `validateK`.
`Tests/Sufficient.lean` exercises `apK` at a `k` strictly larger than the
join (mirroring `bindK`'s own `renderK` case) and `Comp.apK` at a
sufficient grade *pair* each strictly larger than its own component's
join, including both the outer-argument-fails and the inner-fails cases —
the two-coordinate case the step asked to exercise explicitly.

### Accum: an accumulating applicative needs its own carrier

The plan's prediction was **confirmed**: `Graded g α` ([#carrier](#carrier))
holds exactly one error, so a Validation-style `ap` that keeps *every*
failing side has nowhere to put a second error. `Graded/Accum.lean` adds
`Accum (g : Grade Err) (α : Type v)`, a value or a *non-empty* `List Err`
each a member of `g`. This is not a fork of `Graded`
([cpp-counterpart](#cpp-counterpart)'s "never fork a shared definition"):
`Accum` is a different structure with a different law set, indexed by the
*same* `Grade` and the *same* `Grade.join`, connected back to `Graded` by
`toGraded` (first error) — and `Graded` is untouched, used by every step
before and after this one.

> **Provisional.** `Accum`'s error field is a `List Err` with a
> non-emptiness proof, not a `Multiset`. A `Multiset` is the
> mathematically right carrier for an *unordered* bag of errors; `List` is
> the computable one that reduces under `#guard`/`decide` without extra
> tactics, the same reason [#carrier](#carrier) picked `Finset` over an
> abstract order. Revisit if a later consumer needs the errors as a
> genuinely unordered collection.

`Accum.ap (f : Accum g (α → β)) (x : Accum h α) : Accum (Grade.join g h)
β` concatenates both error lists when both sides fail, function's list
first (`es_f ++ es_x`) — matching `ap`'s own argument order and
`Graded.ap`'s short-circuit priority (`ap_err_left`: the function's error
always wins when only one side can be kept). `Accum.map2` is `ap` after
`map`, as in [#applicative](#applicative).

**Property table** — the same shape as `Graded.ap`'s:

| law | property | note |
|---|---|---|
| `Accum.ap_pure_id` | unit (`bot_join`) | identity |
| `Accum.ap_pure_pure` | unit (`bot_join`) | homomorphism |
| `Accum.ap_interchange` | unit (`join_bot` *and* `bot_join`, separately) | interchange |
| `Accum.ap_comp` | unit + associative (`join_assoc`) **+ `List.append_assoc`** | composition |

Confirmed, not just predicted: interchange needed only the two unit
lemmas, stated with the same two-cast technique
[applicative-from-monad] used (`cast (Grade.join_bot g) (ap u (pure a)) =
cast (Grade.bot_join g) (ap (pure (fun f => f a)) u)`, both sides landing
at plain `g`) — no `Grade.join_comm` anywhere in this module, same finding
as `Graded.ap`. `ap_comp` needed one thing `Graded.ap_comp` didn't:
`List.append_assoc`, in the one leaf where `u`, `v`, and `w` all fail —
the left side of the law builds `(es_u ++ es_v) ++ es_w`, the right side
builds `es_u ++ (es_v ++ es_w)`, the same list two different ways. This is
the concrete shape of "accumulation adds a genuinely new proof
obligation": every other leaf of `ap_comp`, and every leaf of the other
three laws, needed nothing beyond what `Graded.ap`'s versions needed.

**`Accum.notMonad`** — the concrete form landed, not the fully general
one: at one witnessing pair of grades (`{e1}`, `{e2}`), for a `bind` left
fully polymorphic in the payload types and in the grades it is applied at
(the same shape `Graded.bind` has), there is no `bind` whose
`bind`/`pure`-derived `ap` equals `Accum.ap`. The witness exploits
`f : Accum {e1} (Unit → Empty)` — `f` fails, and its payload type `Unit →
Empty` is uninhabited, so the continuation any `bind f` call receives is a
function *out of an uninhabited domain*; any two such functions are equal
(there is no point where they could disagree), so `bind f`'s continuation
is the *same term* whether `x` is `.ok ()` or `.errs [e2] ..` — `bind f`
cannot tell the two apart, yet `Accum.ap f x` does (one error vs. two).
**What this does not claim**: it is not the fully general "no *lawful*
Monad instance exists," and the two witness grades needn't even have
`e1 ≠ e2` — the proof never uses that (the contradiction is a list-length
mismatch, `[e1] ≠ [e1, e2]`, true regardless).

**`Accum.toGraded_grade`: the same condition as `ap_flip`, but not, in the
end, load-bearing.** The step's prediction was that `toGraded (ap f x) =
Graded.ap (toGraded f) (toGraded x)` fails when both sides fail, needing
the one-sided restriction [applicative-from-monad] found for `ap_flip`
(`(∃ f', f = .ok f') ∨ (∃ a, x = .ok a)`). `Accum.toGraded_grade` states
exactly that hypothesis, and it **is** the same condition, discharged the
same way (`rcases honeok with ⟨f', rfl⟩ | ⟨a, rfl⟩`) — confirmed. But the
prediction that the theorem *needs* it was **wrong**: `Accum.toGraded_grade'`
proves the equation unconditionally, on every input, including both-fail.
The reason is structural, not coincidental: `Accum.ap`'s concatenation
puts the function's errors first, and `Graded.ap` always keeps the
function's error when the function fails (`ap_err_left`, no condition at
all) — so "first element of the accumulated list" and "the error
`Graded.ap` keeps" are the same error *by construction*. Both theorems are
proved and kept: `toGraded_grade` records that the `ap_flip` condition is
real and sufficient (matching what the step asked for), `toGraded_grade'`
records that, for this particular pair of definitions, it is not
necessary. A different, order-reversed choice of concatenation
(argument's errors first) would have made the one-sided hypothesis load-
bearing instead — the finding is about how `Accum.ap` and `Graded.ap`'s
tie-breaks happen to line up, not a general fact about accumulating
applicatives.

**`Accum.sameGrade`** is not a Lean theorem, just this: `Accum.ap : Accum
g (α → β) → Accum h α → Accum (Grade.join g h) β` and `Graded.ap : Graded
g (α → β) → Graded h α → Graded (Grade.join g h) β` are indexed by the
*same* `Grade` and the *same* `Grade.join` — only the carrier holding the
error differs. Putting the two signatures side by side *is* the theorem.

The consumer, `Examples/Validation.lean`: `parseNatAccum`/
`checkNonEmptyAccum` (grades `{E.parse}`/`{E.range}`, so a "both bad" run
is visibly two different errors, unlike `sumTwo`'s shared `{E.parse}`),
combined by `Accum.map2` into `validateTwoFields`. With both fields bad,
`renderPair (validateTwoFields "abc" "")` guards to `"errs
[Examples.Validation.E.parse, Examples.Validation.E.range]"` — both
errors present, the thing `Graded`'s carrier cannot show.

## traverse

### List: shape-independence is idempotence, spent precisely

`Graded/Traverse.lean` models the C++ `traverse(f, xs)` for a uniform
`f : α → expected<β, error_set<Es...>>`: in C++ its return type is
`expected<vector<β>, error_set<Es...>>`, a grade that does not grow with
`xs`'s runtime length. That signature is only writable because
`error_set`'s union is idempotent, and this module states that as two
separate theorems rather than one, because they cost different things.

`foldGrade (g : Grade Err) : List α → Grade Err` folds `g` once per list
element (`Grade.bot` at the base, `Grade.join g (foldGrade g xs)` at each
`cons`) — the honest, un-widened shape-fold. `traverseRaw f xs : Graded
(foldGrade g xs) (List β)` is `traverse` at that honest grade.

- `foldGrade_le : foldGrade g xs ⊆ g` — **bounded, for free.** Holds for a
  list of any length and needs only the order half of the pomonoid
  (`Grade.join_le`, `Grade.bot_le`); `Grade.join_idem` never appears.
- `foldGrade_cons_ne_nil : xs ≠ [] → foldGrade g xs = g` — **exact, and it
  costs idempotence.** A nonempty list's fold doesn't just stay bounded by
  `g`, it *equals* `g` regardless of length: the one-element base case
  costs `Grade.join_bot`, and every further element costs `Grade.join_idem`
  rather than growing the grade. This is the one law in the whole plan (six
  prior steps: [monad-laws], [applicative-from-monad],
  [applicative-accumulation]) that needed idempotence — every earlier law
  consumed only unit, associativity, and the order.

**The design consequence.** The public `traverse (f : α → Graded g β)
(xs : List α) : Graded g (List β) := widen (foldGrade_le xs) (traverseRaw f
xs)` is defined through `widen` and `foldGrade_le`, *not* through `cast`
and `foldGrade_cons_ne_nil`. That choice is itself the finding: the
*definition* of `traverse` needs only the order — `foldGrade_le` bounds
`foldGrade g []= ⊥` exactly as uniformly as any nonempty list, so the empty
list needs no special case to define `traverse` at all — while the
*precision* claim (the grade `g` isn't padding; every error kind the
signature admits is genuinely reachable) is `foldGrade_cons_ne_nil`, and
that is where idempotence is spent. Defining `traverse` the other way
(`cast` along `foldGrade_cons_ne_nil`) would need idempotence just to
typecheck the empty-list case, which has no elements to be idempotent
over.

`traverse_cons (f : α → Graded g β) (x : α) (xs : List α) : traverse f (x
:: xs) = cast (Grade.join_idem g) (map2 (· :: ·) (f x) (traverse f xs))`
is where idempotence resurfaces at the public API: both `f x` and
`traverse f xs` are already at the uniform grade `g`, so `map2`'s own
grade is `Grade.join g g`, and collapsing that down to `g` again is
exactly `Grade.join_idem`. `traverse_nil : traverse f [] = fromEmpty []`
holds for *every* `f` (`traverseRaw`'s nil case never calls `f`) and needs
no idempotence at all — it is proved directly, the two `⊆`/`=` proofs
standing behind the two sides' `widen`/`fromEmpty` being interchangeable
by proof irrelevance (`widen_irrel`).

Two further theorems: `traverse_map (f : α → Graded g β) (h : γ → α) (xs :
List γ) : traverse f (xs.map h) = traverse (f ∘ h) xs`, by induction using
`traverse_nil`/`traverse_cons` (no new idempotence use — it reuses
`traverse_cons`'s existing cast on each side and cancels); and
`traverse_fromEmpty (xs : List α) : traverse (fromEmpty : α → Graded g α)
xs = fromEmpty xs`, the identity law ("traversing with a context that
cannot fail is the identity"), by induction through the same
`traverse_cons` cast. `traverse_length` (shape preservation — an `.ok`
result has the same length as the input list) is proved from three
`traverse_cons`-derived reduction lemmas (`traverse_cons_ok_ok`,
`traverse_cons_err_left`, `traverse_cons_ok_err`, mirroring
[applicative-from-monad]'s `ap_ok_ok`/`ap_err_left`/`ap_ok_err`); the two
`err`-shaped lemmas also mention `Grade.join_idem`, but only because they
restate `traverse_cons`'s own cast for the error branches specifically —
not a further idempotence cost beyond what `traverse_cons` already pays.

**Scope.** The general non-idempotent case — grades that are not
idempotent under join, or elements each carrying a genuinely different
grade with no uniform `g` — is not modelled here. This is deliberate
scope, not a gap: `foldGrade` and `foldGrade_le` are already stated for an
arbitrary (not-necessarily-idempotent) pomonoid grade and would still
typecheck, but `foldGrade_cons_ne_nil` — the fact that makes the grade
length-independent — is specific to `Grade`'s idempotent join, and no
attempt is made here to state what a non-idempotent grade's traversal
signature would even look like (in C++ terms, it would have to mention
the container's length, which generic code over `error_set` cannot do).

Filled by [traverse-list](../tmp/plan/step-traverse-list.md) (`List`) and
[traverse-tuple](../tmp/plan/step-traverse-tuple.md) (fixed-size, below).

### The sufficient-grade layer

**The fold disappeared. There is no `foldGradeK` anywhere in
`Graded/Sufficient.lean`, and [sufficient-grade-traverse] never found a
reason to write one.** `foldGrade` and `foldGrade_cons_ne_nil` exist to
answer a question only worth asking when the return grade is *computed*
by folding: does joining `g` into itself once per list element, for a
length not known until runtime, ever exceed `g`? At a caller-nominated
sufficient grade `k`, nothing folds — every element lands at `k` directly,
via the same `hg : g ⊆ k` reused at every position:

```lean
def traverseK (hg : g ⊆ k) (f : α → Graded g β) : List α → Graded k (List β)
  | []      => pureK []
  | x :: xs => map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x) (traverseK hg f xs)
```

`traverseK_nil` and `traverseK_cons` (added by [obligation-layering] as a
bounded probe) are both `rfl`. This step confirms the probe was not
already the migration by building the analogues it explicitly deferred:

| law (union-graded → sufficient-grade) | casts in statement (before → after) | proof lines (before → after) | property consumed |
|---|---|---|---|
| `traverse_cons` → `traverseK_cons` | 1 (`Grade.join_idem`) → 0 | 13 → 3 (`rfl`) | idempotent → none |
| `traverse_map` → `traverseK_map` | 0 → 0 | 8 → 8 | idempotent (via `traverse_cons`, cancels) → none |
| `traverse_fromEmpty` → `traverseK_fromEmpty` | 0 (statement); proof itself casts along `Grade.join_idem` → 0 | 10 → 7 | idempotent → none |
| `traverse_cons_ok_ok` → `traverseK_cons_ok_ok` | 0 → 0 | 6 → 4 | idempotent (delegated) → none |
| `traverse_cons_err_left` → `traverseK_cons_err_left` | proof transports a membership proof along `Grade.join_idem g` → 0 | 8 → 4 | idempotent → none |
| `traverse_cons_ok_err` → `traverseK_cons_ok_err` | same as above → 0 | 8 → 5 | idempotent → none |
| `traverse_length` → `traverseK_length` | 0 → 0 (both; the union-graded one inherits its casts from the three reduction lemmas above, not its own statement) | 24 → 22 | idempotent (via delegates) → none |
| `traverse_nil` → `traverseK_nil_eq_fromEmpty` | 0 → 0 | 3 → 1 (`rfl`) | none → none |
| (no union-graded counterpart) | — | `traverseK_irrel`: 1 (`rfl`) | — → none |

Every "after" proof cites no property at all — not a cheaper property,
none — confirming [obligation-layering]'s classification of
`foldGrade_cons_ne_nil`, `traverse_cons`, `traverse_cons_err_left`,
`traverse_cons_ok_err`, and `traverse_fromEmpty` as canonicalization: each
one's idempotence citation was spent identifying two spellings of the
*union-graded traversal's own* grade, never picking a value, and never a
fact `traverseK` needs to compute anything at all.

**Length-independence is not a theorem here, the way `foldGrade_cons_ne_nil`
is one for `traverse` — it is a property of `traverseK`'s own signature.**
`traverseK hg f : List α → Graded k (List β)` names the same output grade
`k` for every list before a single theorem is stated about it. What
survives as an actual theorem is the narrower, still-true fact `traverseK_length`
states: an `.ok` result's *payload* has the input list's length — shape
preservation, not grade preservation, exactly the distinction
[traverse-tuple]'s own "shape preservation is by construction" note
already drew for the fixed-size case.

**`traverseK_irrel`** (`traverseK hg f xs = traverseK hg' f xs`, any two
proofs of `g ⊆ k`) is `rfl` — the mirror of `bindK_irrel`, with only one
witness to be irrelevant about, since `traverseK` reuses `Grade.le_refl' k`
at every position for the accumulated tail rather than threading a second
inclusion per element.

**The ∅-grade case.** `traverseK_nil` (`traverseK hg f [] = pureK []`)
already *is* the sufficient-grade analogue of `traverse_nil`, since
`pureK` is `fromEmpty` by definition; `traverseK_nil_eq_fromEmpty` states
it in `traverse_nil`'s own spelling. Where `traverse_nil` needed
`fromEmpty_eq_ok` plus a proof-irrelevance argument between two different
`⊆ ∅ → g`-shaped inclusions standing behind each side's `widen`, there is
no fold here to be uniform with in the first place: `traverseK hg f []`
never mentions `foldGrade_le`, so the whole thing is `rfl`.

**`traverse_eq_traverseK`, the bridge** (tagged `BRIDGE`), instantiates
`traverseK` at the *tightest* sufficient grade — `g` itself, along
`Grade.le_refl' g` — and recovers `traverse`. This is the one place in
this subsection idempotence still appears, and it appears for the same
reason [obligation-layering] already found everywhere else: `traverse`'s
own cons case computes through `Grade.join g g` and identifies it with
`g`, and the bridge's induction has to go through that identification on
the union-graded side to line the two traversals up. The idempotence is
not reconciling `traverse` against `traverseK` — it is `traverse`
reconciling two spellings of its *own* grade, exactly as `traverse_cons`
already pays it, with `traverseK` sitting outside that reconciliation
entirely (its own side of the bridge's induction step is `rfl`
throughout).

**Verdict, extending [sufficient-grade-bind]/[sufficient-grade-applicative]/[obligation-layering]
to the last operational law standing.** The traversal leg is not merely
cheaper at the sufficient grade, the way `bindK`/`apK` were: the function
that existed to compute the exact grade, and the theorem that existed to
prove that computation exact, have no analogue to be cheap or expensive.
Every remaining idempotence citation in the model
([obligations](#obligations)'s table) is now confirmed, leg by leg, to be
about a grade's spelling and never about a traversal, a bind, or an
apply's *value* — [sufficient-grade-morphism] and
[sufficient-grade-nested] are what is left to check this against.

### Tuple: the grade is computed once, at the type level

`Graded/Tuple.lean` models the C++ `transpose(tuple<expected<A,
error_set<X>>, expected<B, error_set<Y>>>)` → `expected<tuple<A,B>,
error_set<X,Y>>` case. Unlike `List`'s `traverse`, a tuple's elements carry
*different* grades and *different* payload types, so there is no single
uniform `g` to fold a fixed number of times — the joined grade is a static
fold over the *list of element grades*, computed once from the tuple's
shape, not a runtime-length-dependent fold of one repeated grade.

**Representation.** `GList gs αs` holds one `Graded g α` per tuple slot, `g`
drawn from `gs` and `α` from `αs` in lockstep — the fully heterogeneous
representation the step called for, not the simpler uniform-payload
fallback (elements genuinely differ in both grade *and* type; see the
consumer below). It is defined as a plain recursive `def` over the two
index lists together (`PUnit` at `[],[]`, `Graded g α × GList gs αs` at
each matched `cons`, the uninhabited `PEmpty` at a length mismatch), not as
a genuine `inductive` family.

> **Finding, not in the step brief.** The literal sketch (`inductive GList
> : (gs) → (αs) → Type _ | nil | cons : Graded g α → GList gs αs → GList
> (g :: gs) (α :: αs)`) does not typecheck as an `inductive`: Lean's
> large-inductive-family check requires the resultant sort to dominate not
> just `Graded g α`'s own level `v`, but the level of `α`'s *type*
> (`Type v`'s type is `Type (v+1)`), since `α` is quantified fresh per
> constructor rather than fixed once as a global parameter (contrast
> `Sigma {α : Type u} (β : α → Type v) : Type (max u v)`, where `α` is a
> parameter and pays no such tax). Declaring `GList` as an `inductive`
> would force `Type (max (u+1) (v+2))` or worse. The `def`-as-nested-Prod
> route sidesteps this entirely — a plain recursive `Type`-valued function
> carries no large-elimination obligation — and is the same trick `HList`
> below already uses. This cost nothing observable to the consumer:
> `GList.nil`/`GList.cons` are ordinary `def`s standing in for
> constructors, and `sequence`'s equations below are still `rfl`.

`HList αs` (`Graded/Prelude.lean`) is the plain heterogeneous product
`sequence` lands its payload in: `HList [] = PUnit`, `HList (α :: αs) = α ×
HList αs`. Checked against Mathlib at the pinned version first:
`List.TProd` (`Mathlib.Data.Prod.TProd`) builds the same shape of iterated
product, but over an arbitrary index type `ι` and family `π : ι → Type*` —
instantiating `ι := Type v`, `π := id` buys nothing over a direct
three-line `def` and loses the `HList.nil`/`HList.cons` names `sequence`'s
equations are stated with. Written fresh, as a shared definition in
`Graded/Prelude.lean` (every later module imports it), for the same
universe reason `GList` above is a `def` and not an `inductive`.

**`joinAll`** (`List (Grade Err) → Grade Err := List.foldr Grade.join
Grade.bot`) is a *different* function from `Graded.Traverse.foldGrade`,
not a fork of it: `foldGrade g xs` folds one fixed grade `g` once per list
element; `joinAll gs` folds a list of *distinct* grades, one per tuple
slot, and takes no `g` argument at all. The two are conceptual siblings
("fold `Grade.join` over a list, `Grade.bot` at the base") with no shared
code and no intent to unify them.

**Property table** — the tuple's fold splits along exactly the axis the
step predicted:

| law | property | note |
|---|---|---|
| `joinAll_perm` | commutative + associative | order-independence — typeability |
| `joinAll_dedup` | idempotent (via `join_mem_eq`) | dedup — tidiness, not typeability |

`joinAll_perm : gs ~ gs' → joinAll gs = joinAll gs'` needs only
`Grade.join_comm`/`Grade.join_assoc`, proved by induction on the
permutation witness (`nil`/`cons`/`swap`/`trans`, the same case shape as
Mathlib's `List.Perm.foldr_eq`) rather than through a
`Std.Commutative`/`Std.Associative` instance (`List.Perm.foldr_op_eq`
would need one) — citing the named `Grade` lemmas keeps `join_comm`'s use
greppable, the same reason [#grade](#grade) never registers `Grade` as a
Mathlib lattice instance. **This is the theorem that licenses the C++
claim `error_set<X,Y>` ≡ `error_set<Y,X>`.** The C++ canonical sorting of
`error_set`'s type arguments is an *implementation* of `joinAll_perm`, not
the theorem itself — sorting is one way to make the union order-
independent at the representation level; commutativity plus associativity
is *why* any such implementation is licensed to exist at all. As with
[applicative](#applicative)'s four laws, no idempotence is needed here:
confirms the step's own prediction.

`joinAll_dedup : joinAll gs.dedup = joinAll gs` needs `Grade.join_idem`,
spent in one place: `join_mem_eq (g ∈ gs) : Grade.join g (joinAll gs) =
joinAll gs`, where finding `g` already present collapses `Grade.join g g`
to `g`. This is tidiness, not typeability — dropping a duplicate grade
from the list changes nothing observable about the joined grade, but
*proving* that costs the property the `List` case's `foldGrade_cons_ne_nil`
also needed. Confirms the step's prediction, mirroring
[traverse-list](../tmp/plan/step-traverse-list.md)'s split precisely:
order-independence is free of idempotence, tidiness is not.

**Shape preservation is by construction, not a theorem.** `sequence :
GList gs αs → Graded (joinAll gs) (HList αs)` is indexed by `αs`
throughout — the payload shape never changes because there is no
per-length recursion to preserve anything *across*, unlike `List`'s
`traverse_length`. Stating a "shape preservation" theorem for the tuple
case would be proving that `αs = αs`, which is not a finding.

The consumer, `Examples/Validation.lean`: `validateTuple s n` sequences
`parseNat s : Graded {E.parse} Nat`, `checkRange n : Graded {E.range}
Nat`, and `logIt n : Graded {E.io} Unit` — three elements with three
different grades and two different payload types (`Nat`, `Nat`, `Unit`) —
into one `Graded {E.parse, E.range, E.io} (HList [Nat, Nat, Unit])`,
accepted definitionally against the literal-union ascription the same way
`validate`'s `bind`-computed grade is. `#check` displays exactly that
union grade. A failure in the *middle* element (`checkRange 9999`, with
`parseNat` succeeding) surfaces as `E.range` — `sequence`'s
`map2`/`ap`-derived short-circuiting reaches the second element's error
before ever forcing the third.

## compose

`Graded.flatten : Graded g (Graded h α) → Graded (Grade.join g h) α` (in
`Graded/Compose.lean`) collapses a nested carrier to a single one. C++
routinely collapses `expected<expected<T, error_set<Es1...>>,
error_set<Es2...>>` to `expected<T, error_set<Es1..., Es2...>>` and treats
it as obviously safe; `flatten` is that collapse, made precise.

**Product pomonoid, not a flat union.** The nested carrier's *natural*
grade is the *pair* `(g, h)` — two genuinely different layers, an outer
one and an inner one, tracked separately until something identifies
them. `flatten`'s target grade `Grade.join g h` is that identification:
it is where the pair collapses to one `Finset`, not where it started.
Every theorem below is about what survives the collapse.

**`flatten` is the monad's own multiplication.** `flatten_eq_bind_id :
flatten x = bind x (fun y => y)` says so directly: `flatten` is not a
second primitive needing its own proofs from scratch, it is `bind`
applied to the identity continuation. Every compatibility law below is
really a [monad](#monad) law in disguise, and reads that way:

- `flatten_map` (naturality): mapping the inner payload before
  flattening agrees with flattening then mapping outside.
- `flatten_pure_outer`, `flatten_pure_inner` (unit, `Grade.bot_join` /
  `Grade.join_bot`): wrapping either layer with `pure` and flattening
  recovers the other layer untouched — an empty-graded layer contributes
  nothing to the union.
- `flatten_flatten` (associative, `Grade.join_assoc`): flattening the
  outer two layers of a *triple*-nested carrier first, or the inner two
  first (via `map flatten`), agree — the same fact `bind_assoc` states
  for sequencing, here for nesting.
- `flatten_widen_outer`, `flatten_widen_inner` (order, `Grade.join_mono`):
  widening either layer before flattening agrees with flattening then
  widening the joined result. Both are proved by plain `rfl` case
  analysis — no `cast` at all, since widening produces an inclusion
  between grades, not an equation, exactly as `Widen.widen_map` needed
  none.

**A universe wrinkle, resolved.** `Graded h α` (the inner carrier) lives
in `Type (max u v)`, not `Type v` — a genuinely higher universe than the
bare payload `α`. `Monad.bind`'s declared signature ties its own two
payload type-variables to a single shared universe, so calling it on a
value whose payload is itself a `Graded` (as `flatten_eq_bind_id` and
`flatten_flatten` both need) only typechecks when that shared universe
equation is satisfiable. `Graded/Compose.lean` quantifies its own
payloads at `Type u` — the same universe as `Err` itself — rather than
this codebase's usual separate `Type v`, specifically so `max u u = u`
resolves the constraint definitionally. This is local to `Compose.lean`;
no other module's universes changed.

**`flatten_comm` needs *no* hypothesis — a genuinely different answer
than the question expected.** The "at most one side is an error"
condition has appeared twice before this step: `ap_flip`'s hypothesis
`(∃ f', f = .ok f') ∨ (∃ a, x = .ok a)`
([applicative](#applicative)), and again in the accumulating
applicative's laws. Both needed it because `ap`/`apFlipped` combine two
*independent* graded values, each of which can independently be an
error — which one's error survives the reordering is a genuine question.
`flatten x = cast (Grade.join_comm h g) (flatten (swap x))` needed no
such hypothesis, and not because it is a third confirmation of the same
condition stated differently: `Graded g (Graded h α)` is not two
independent values, it is *one* value, nested, and it has exactly three
inhabited shapes (`ok (ok _)`, `ok (err _ _)`, `err _ _`) — never two
errors at once, by construction. The condition that mattered for
`ap_flip` is true of every `flatten`/`swap` input *vacuously*, so it
never needed writing down. Proved unconditionally by case analysis, each
case closing by `cast_ok`/`cast_err` plus the ambient proof irrelevance
on `Finset` membership.

**The traverse composition law is false, not merely hard.** The
"cleanest form that typechecks" —
`flatten (map (traverse k) (traverse f xs)) = traverse (fun a => flatten
(map k (f a))) xs` — is refuted by a concrete counterexample (recorded in
[blocked-compose-flatten](../tmp/plan/blocked-compose-flatten.md)): the
left side commits to *all* of `f` across the whole list before ever
consulting `k` (so a later position's `f`-failure wins over an earlier
position's `k`-failure), while the right side flattens `f` and `k`
together at each position before traversing (so `traverse`'s own
left-to-right short circuit sees whichever position fails first,
regardless of which function caused it). These are different
algorithms, and they disagree exactly when an earlier element's `k`
fails while a later element's `f` also fails. The classical Traversable
composition law is true for a *`Compose F G`*-aware traversal, which
keeps the two layers distinct until the very end; `Graded g'` conflates
"which layer failed" into one flat grade the moment a value is
constructed, so no per-element `flatten`-then-traverse on one flat
carrier can recover the priority a genuine `Compose`-aware traversal
gives the outer layer. Settling this needs an applicative/traversable
instance for genuinely composed (unflattened) functors — out of this
step's scope; not attempted here beyond the counterexample.

### Comp: the product-graded composite, kept genuinely nested

`Graded/ComposeApp.lean` builds the structure the classical composition
law is actually about: `Comp g h α := Graded g (Graded h α)`, the same
nested carrier `flatten` collapses, but indexed by the *pair* `(g, h)` —
outer and inner, joined componentwise in the product pomonoid, never
identified into one `Finset`. `Comp.ap` combines two `Comp` values by
running the *outer* `Graded.ap` with the *inner* `Graded.ap` lifted inside
as the combining function — exactly `Compose`'s own applicative instance,
specialised to this carrier — landing at `Comp (g ⊔ g') (h ⊔ h')`.
`Comp.pure`, `Comp.map`, `Comp.map2` are the expected liftings; two small
double-indexed transport helpers, `Comp.widenGH` and `Comp.castGH`, apply
`Graded.widen`/`Graded.cast` once per component and are used throughout
rather than a single-layer `cast`/`widen`, following [applicative-from-monad]'s
two-cast technique doubled.

**The four applicative laws hold, and need exactly what the single-layer
law needed, in each component independently.** `Comp.ap_pure_id`,
`ap_pure_pure`, `ap_interchange`, `ap_comp` are each proved by citing the
*inner* `Graded.ap` law directly (`Graded.ap_pure_id F`, etc.) on an
opaque inner value, after casing only the *outer* shape of each `Comp`
argument — the inner value is never itself case-split for these four laws.
**No law needed any relationship between `g` and `h`** (or `g'` and `h'`):
every cast cites a property of one component's own grades, matching
[applicative-from-monad]'s finding exactly, doubled. `join_comm` appears
nowhere in the four laws, same as the single-layer case.

**`traverseComp` and the law this step exists for.** `traverseComp (f : α
→ Comp g h β) (xs : List α) : Comp g h (List β)` is built the way
`Graded.traverse` was: an honest per-element-folded raw traversal
(`Comp.traverseRaw`, reusing `Graded.foldGrade`/`foldGrade_le` once per
component — no second `foldGrade`), widened once via `Comp.widenGH` along
`foldGrade_le` in each component, so the empty list needs no special
case. `traverseComp_eq` is the law:

```lean
theorem traverseComp_eq (f : α → Graded g β) (k : β → Graded h γ) (xs : List α) :
    traverseComp (fun a => map k (f a)) xs = map (traverse k) (traverse f xs)
```

**This holds, unconditionally, no hypothesis.** No `flatten` appears in
its statement, and both sides live in `Graded g (Graded h (List γ))` with
the two grades kept separate throughout. This is recognisably Mathlib's
`LawfulTraversable.comp_traverse` (`Mathlib.Control.Traversable.Basic`):
`traverse (Functor.Comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f)
(traverse g x))`, with Mathlib's `g` (applied first) matching this
theorem's `f`, Mathlib's `f` (applied second) matching this theorem's `k`,
and `Comp.mk` — Mathlib's marker constructor for keeping two functors
distinct — omitted because `Comp g h α`'s *indices* already keep the
layers apart, with no wrapper needed. The proof needed `Graded.traverse_cons`
(hence `Grade.join_idem`, once per component, exactly mirroring
`traverse_cons`'s own cast) plus the reduction lemmas `Comp.ap_ok_ok`/
`ap_err_left`/`ap_ok_err` and `Graded.ap_ok_ok`/`ap_err_left`/`ap_ok_err` —
no new property beyond what [traverse-list] and this step's own
applicative laws already established, and no `join_comm`.

**So P3200's composition claim is fine, provided it is stated about the
unflattened, product-graded pair — never about a single flat grade.**
[compose-flatten]'s counterexample refuted the flattened form; this
theorem is the form that was actually true all along, and the two
results are not in tension: they are about different structures.

**`flatten_ap`: the explanation for [compose-flatten]'s counterexample.**
Is `flatten` an applicative morphism from the product-graded composite to
the union-graded carrier?

```lean
theorem flatten_ap (ff : Comp g h (α → β)) (xx : Comp g' h' α)
    (hcond : (∃ e he, ff = Graded.err e he) ∨ (∃ f', ff = Graded.ok (Graded.ok f')) ∨
      (∃ X, xx = Graded.ok X)) :
    flatten (Comp.ap ff xx) = cast (Comp.grade_reassoc ..) (ap (flatten ff) (flatten xx))
```

**Holds only under `hcond`, and fails outright without it — a genuine,
`#eval`-confirmed counterexample, not merely an unproved case.** The grade
side needs both `Grade.join_assoc` *and* `Grade.join_comm` to reassociate
`(g ⊔ h) ⊔ (g' ⊔ h')` into `(g ⊔ g') ⊔ (h ⊔ h')`, making it
one of six theorems that consume `Grade.join_comm` (`ap_flip`, `flatten_comm`, `Comp.grade_reassoc`, `joinAll_perm`, `join_mem_eq`, and the generic `joinAllG_perm`). The *value* side fails
for a structural reason distinct from `ap_flip`'s: `Comp.ap`'s own
short-circuit order is outer-`ff`-error, then outer-`xx`-error, then
`ff`'s inner error, then `xx`'s inner error; flattening each side first
and combining with the single-layer `ap` gives outer-`ff`-error, then
`ff`'s inner error (exposed the moment `ff` alone is flattened), then
outer-`xx`-error — the middle two swap. The one case where this matters —
`ff` is outer-`ok` with a *failing* inner payload, while `xx`'s outer
layer *also* fails — is exactly where the two orders disagree: `Comp.ap`
reports `xx`'s outer error (it never looks past `xx`'s outer failure to
notice `ff`'s inner one); flatten-then-`ap` reports `ff`'s inner error.
`hcond` is precisely "that case does not arise." This is not a third
confirmation of `ap_flip`'s "at most one side is an error" condition — it
is a genuinely different comparison (the nested carrier's own short-circuit
order against the flattened carrier's), that happens to also need a
disjunctive hypothesis.

**This is the exact mechanism behind [compose-flatten]'s counterexample.**
`Examples/Validation.lean` puts both sides of the *naive* law on one
screen at the same two inputs (`checkRange` failing *early*, at position
0; `parseNat` failing *late*, at position 1): `flatten (traverseComp (fun
a => map checkRange (f a)) xs)` — which by `traverseComp_eq` equals the
naive law's left side — reports the *late* `parseNat` failure (`E.parse`);
`traverse (fun a => flatten (map checkRange (f a))) xs` — the naive law's
right side — reports the *early* `checkRange` failure (`E.range`). They
disagree, confirming [compose-flatten]'s finding; and now there is an
explanation: the unflattened `traverseComp` reports its outer and inner
grades separately (`renderComposed` shows `E.range` as an *inner* error,
distinct from an *outer* `E.parse`), and `flatten_ap`'s failure is exactly
what is lost by collapsing that distinction in either order.

### graded-traversable-composition

**Question.** Does a graded Traversable satisfy the classical
composition law, and if not, what is the right statement of it?

**Status: CLOSED.** Answered by [compose-flatten] (the flattened form is
false) and [compose-applicative] (the product-graded form is true,
unconditionally). See `tmp/plan/blocked-compose-flatten.md` for the
flattened counterexample's full record, and [#compose](#compose)'s `Comp`
subsection for the product-graded law, `traverseComp_eq`, and the
`flatten_ap` explanation.

**What is settled.** The naive single-carrier form

```lean
flatten (map (traverse k) (traverse f xs)) = traverse (fun a => flatten (map k (f a))) xs
```

is **false**, refuted by a counterexample confirmed with `#eval`, not by
hand-argument. `flatten (map (traverse k) (traverse f xs))` runs every
element's outer stage before any inner stage; `traverse (fun a => flatten
(map k (f a))) xs` interleaves the two per element. When an earlier
element's inner stage fails and a later element's outer stage also fails,
the two report different errors from different positions.

**What is settled about its scope.** The refutation is **not** a fact
about grading. Re-run at a single grade `g = h`, so both sides sit at the
same grade and only the values can differ, the two sides still disagree.
The same counterexample refutes the same naive law for an ungraded nested
`expected<expected<T, E>, E>`. The cause is `flatten` destroying the
distinction between layers, which an ordinary `Either` flattening does
just as thoroughly. So this is evidence that flatten-then-traverse is the
wrong shape for a composition law, graded or not — it is not evidence
against graded traversables.

**What is now settled: the product-graded form.** The classical
composition law is about `Compose F G` — two functors kept *separate*.
For graded functors the natural grade of `Graded g (Graded h α)` is the
**pair** `(g, h)` in the product pomonoid, not the union. `Comp g h α :=
Graded g (Graded h α)` ([#compose](#compose)'s `Comp` subsection) is that
structure, built and tested: `Comp.ap` combines outer layers with the
outer `Graded.ap` and inner layers with the inner `Graded.ap` lifted
inside, exactly `Compose`'s own instance, and

```lean
theorem traverseComp_eq (f : α → Graded g β) (k : β → Graded h γ) (xs : List α) :
    traverseComp (fun a => map k (f a)) xs = map (traverse k) (traverse f xs)
```

holds **unconditionally** — no `flatten`, no hypothesis, both sides kept
nested. It is recognisably Mathlib's `LawfulTraversable.comp_traverse`
(`Mathlib.Control.Traversable.Basic`), and its proof consumed nothing
beyond `Grade.join_idem` (once per component, via `Graded.traverse_cons`)
and the applicative reduction lemmas — no `Grade.join_comm` anywhere. So
the answer to the question above is: **yes**, a graded Traversable
satisfies the classical composition law, stated against the product-graded
composite; **no**, it does not satisfy the flattened form, which is a
different (and false) statement. Reading [compose-flatten]'s refutation as
a result about graded traversables in general was the generalization to
avoid, and it was wrong to draw — this step's own law is the counter-
demonstration.

**The explanation for the flattened form's falsity.** `flatten_ap` asks
whether `flatten` is an applicative morphism from the product-graded
composite to the union-graded carrier, and the answer is **conditional**:
it holds under a one-sided hypothesis (`Comp.grade_reassoc`'s reassociation
needs both `Grade.join_assoc` and `Grade.join_comm`, making it
one of six theorems that consume `Grade.join_comm` (`ap_flip`, `flatten_comm`, `Comp.grade_reassoc`, `joinAll_perm`, `join_mem_eq`, and the generic `joinAllG_perm`) — and the
*value* side needs "`ff`'s outer layer fails, or `ff` succeeds all the way
through, or `xx`'s outer layer succeeds"), and it **fails outright**
without that hypothesis, confirmed by `#eval`. The failing case is exactly
the shape [compose-flatten]'s own counterexample needed: `ff` outer-`ok`
with a failing inner payload, while `xx`'s outer layer also fails —
`Comp.ap`'s own short-circuit never looks past `xx`'s outer failure to
notice `ff`'s inner one, while flatten-then-`ap` sees `ff`'s inner failure
the moment `ff` alone is flattened. `Examples/Validation.lean` puts both
sides of the *naive* flattened law on one screen at inputs matching this
exact shape (`checkRange` failing early, `parseNat` failing late) and
confirms they disagree, with `traverseComp`'s own separately-graded
answer showing which layer is actually responsible for each.

**What this costs P3200 today: it can now state the composition law, but
only about the unflattened pair.** [cpp-counterpart](#cpp-counterpart)
claims only that `traverse` is shape-preserving over ranges and over
tuples; it makes no composition claim yet, so nothing existing changes.
But if P3200 ever wants a composition claim, the true statement is: "the
composed traversal computed with the two grades kept separate agrees with
composing the two `traverse` calls" — never "flatten first," since that
collapse is proved lossy by `flatten_ap`'s own failing case.

**Log.**

- 2026-09-08 — [compose-flatten] refuted the naive form; recorded the
  counterexample, the mechanism, and what a faithful version would cost.
  Everything else in the step merged; only this law is open.
- 2026-09-08 — orchestrator re-ran the counterexample at a single grade
  and confirmed the failure is independent of grading. Narrows the
  finding: it is about flattening, not about grades.
- 2026-09-08 — separated "the flattened law is false" (settled) from "the
  product-graded law" (never tested), after the record was read as
  refuting graded traversable composition, which it does not. Confirmed
  [cpp-counterpart](#cpp-counterpart) makes no composition claim, so
  nothing in the C++ design currently depends on the answer.
- 2026-09-08 — [compose-applicative] added to the plan as step 13 to
  answer this, and `step-compose-flatten.md` amended so a re-run of the
  plan cannot repeat the substitution of the flattened question for this
  one.
- 2026-09-08 — [compose-applicative] built `Comp g h α`, the product-graded
  composite, and proved `traverseComp_eq` (the classical composition law,
  stated against the unflattened pair) holds unconditionally, consuming
  only `Grade.join_idem` per component and no `join_comm`. Proved
  `flatten_ap` (is `flatten` an applicative morphism from the composite to
  the union-graded carrier?) holds only under a one-sided hypothesis and
  fails outright without it, confirmed by `#eval` — the precise mechanism
  behind [compose-flatten]'s counterexample. Status changed to CLOSED:
  both halves of the question (flattened form false, product-graded form
  true) are now settled, and they are not in tension because they are
  statements about different structures.

## morphisms

`Graded/Morphism.lean` answers the question `traverse`'s naturality law
needs answered: what does a morphism between graded structures *do to the
grade*? The C++ instance is `transform_error`-style renaming/coarsening —
`error_set<A, B> → error_set<C>` by sending both `A` and `B` to `C` — and
this section is the law set behind it.

**`Grade.rename := Finset.image φ` is a join-semilattice homomorphism,
unconditionally.** `Grade.rename_join` (`Finset.image_union`) and
`Grade.rename_bot` (`Finset.image_empty`) hold for *any* `φ : Err → Err'`
— no injectivity, no surjectivity, nothing beyond `φ` being a plain
function. Tagged `/-- PROPERTY: homomorphism -/` per
[oracle-export](../tmp/plan/step-oracle-export.md)'s grep. `Finset.image`
does **not** preserve meet or complement — this design never asked it to;
"homomorphism of join-semilattices" is the precise claim, not "lattice
homomorphism." `Grade.rename_mono` (order preserved, from
`Finset.image_subset_image`) is the corresponding order-level fact, also
unconditional.

**A restated Mathlib lemma was load-bearing, for an elaboration reason
worth recording.** `Finset.mem_image_of_mem φ he : φ e ∈ Finset.image φ g`
has its type *fully determined by its own arguments* — no expected-type
propagation reaches it — so embedding it directly inside a `Graded.err`
constructor produces a term indexed by `Finset.image φ g`, not by
`Grade.rename φ g`, even though the two are definitionally equal. Later
`rw`/`simp` calls against lemmas stated in terms of `Grade.rename` then
fail to match it (syntactic, up to reducible transparency, not full
defeq). The fix, `Grade.mem_rename`, is the same fact re-stated as a
named `theorem` whose own signature pins the conclusion's type to
`Grade.rename φ g`; every downstream `Graded.err` term is built from that
theorem instead of the raw Mathlib lemma. This is a general pattern for
this codebase, not specific to renaming: naming a borrowed fact under
your own vocabulary is not cosmetic once dependent indices are involved.

**Carrier-level `rename`** lifts `φ` to `Graded g α → Graded (Grade.rename
φ g) α`: `ok` untouched, `err` pushed through `φ` and `Grade.mem_rename`.
It is natural in the payload (`rename_map`, no cast — the grade is fixed
on both sides) and commutes with `widen` (`rename_widen`, along
`Grade.rename_mono`) and `cast` (`rename_cast`, along the image of the
grade equality). It is a monad morphism: `rename_bind` and `rename_pure`
commute with `bind`/`pure` up to `Grade.rename_join`/`Grade.rename_bot`
transporting the joined/unit grade — the same "cast on the undistributed
side" convention every `bind`/`ap` law in this codebase uses. `rename_ap`
and `rename_map2` give the same fact for the applicative operations,
proved directly from `ap`'s reduction lemmas rather than by unfolding
through `bind`.

**`GradedHom`: the general definition.** A graded monad morphism is a
join-semilattice homomorphism on grades (`gmap_join`, `gmap_bot`)
together with a carrier-level family, natural at every grade and payload
type, that commutes with `bind`/`pure` up to that homomorphism
(`hom_bind`, `hom_pure`). `renameHom` packages `Grade.rename`/`rename` as
the one instance the C++ design actually uses.

> **Provisional.** `GradedHom` asks nothing of `gmap`/`hom` beyond the
> above — no injectivity, no surjectivity. Every law in this file,
> including the `traverse` naturality law below, went through for an
> arbitrary `φ`, including the deliberately many-to-one coarsening
> exercised in `Examples/Validation.lean` (`{E.parse, E.range} → {E'.bad}`
> via a constant function). Revisit only if a later consumer needs to
> *recover* the source grade from the target one (needs injectivity) or
> needs every target grade hit (needs surjectivity) — neither arises here.

**Naturality of `traverse` against `rename`, unconditionally.**
`traverse_rename : rename φ (traverse f xs) = traverse (rename φ ∘ f) xs`
needs **no top-level cast** — unlike `rename_bind`/`rename_ap`, `traverse`
fixes its result at the exact grade `g` (via `widen`, not `bind`'s
`join`), so both sides live at `Grade.rename φ g` outright. The proof, by
induction using `traverse_cons`, does need `rename_cast` and
`rename_map2` internally to push `rename` through the `Grade.join_idem`
cast `traverse_cons` carries, and those internal casts cancel by proof
irrelevance (any two proofs of the same grade equality give the same
`cast`, the same fact `Widen.widen_irrel` states for `widen`) rather than
by an extra rewrite — `widen_irrel` itself is not cited, but the
reasoning it names is exactly what closes the induction step.

**No "at most one side is an error" hypothesis anywhere in this file —
correctly.** `ap_flip` ([applicative](#applicative)) and `Accum`'s laws
needed that hedge because they compare two *independent* graded values
that can each independently fail. `rename` never compares two things; it
transports one value through a fixed map, so there is only ever one side.
This is the same distinction [compose-flatten](#compose) drew for
`flatten_comm`: the hedge is for genuine independence, not a pattern to
reach for on sight.

**`rename_toGraded` was kept, not dropped.** The step file allowed
dropping it if it grew past a few lines; `Accum.rename` (map `φ` over the
error list, `List.mem_map`/`List.map_eq_nil_iff` for the two side
conditions) and `Accum.rename_toGraded` (both sides reduce by `rfl` once
`es` is split into `nil`/`cons`, since `(e :: es).map φ = φ e :: es.map φ`
definitionally) together came to about a dozen lines, so both are in
`Graded/Morphism.lean`.

**Consumer.** `Examples/Validation.lean` coarsens `validate`'s
`{E.parse, E.range}` down to a single `E'.bad` via `coarsen : E → E'`
(a constant function, deliberately non-injective); `Grade.rename coarsen
{E.parse, E.range} = {E'.bad}` computes via `#guard`, and renaming
`validate`'s three outcomes collapses both failure kinds to the one
target error while leaving the success case untouched.

## representation

`Graded/Canonical.lean` builds the representation the C++
`error_set<Es...>` actually uses and connects it to `Grade`
(`docs/design.md#grade`), which every other module in this codebase
builds on. **This is a representation theorem about `Grade`, not a
second grade.** It replaces `Grade` nowhere: `Canon` has no `pure`,
`bind`, `join`, or `bot` of its own, and every consumer
(`Examples/Validation.lean`) stays on `Finset` unchanged. What it adds is
a proof that a second, order-dependent spelling of the same data
(`Canon`) is interchangeable with the first (`Grade`), via `canonEquiv`.
Read this paragraph before reading `Canon` as a fork of `Grade` — it is
not one.

**`Canon Err := { l : List Err // l.SortedLT }`** (`Graded/Canonical.lean`)
— a strictly-`<`-increasing list of error kinds, at a `[LinearOrder Err]`.
`List.SortedLT` (this codebase's pinned Mathlib's name for "strictly
monotonic"; there is no `List.Sorted` at this commit — see
`canon_requires_linear_order` below for why lemma names had to be
re-checked here) already forces every element distinct
(`List.SortedLT.nodup`), so it is "sorted, no duplicates" in one
predicate rather than two. Declared `abbrev`, matching `Grade`'s own
`abbrev`, so instance search sees through to the underlying `Subtype`'s
`DecidableEq` etc. rather than needing them re-derived by hand.

- `Canon.ofFinset : Finset Err → Canon Err` sorts (`Finset.sort`, whose
  default relation `≤` is already `SortedLT` at a linear order —
  `Finset.sortedLT_sort`).
- `Canon.toFinset : Canon Err → Finset Err` forgets the order
  (`List.toFinset`). **This direction's proof needs only
  `[DecidableEq Err]`** — order plays no part in "which elements are
  present" — even though its *signature* carries `[LinearOrder Err]`,
  because that is what is needed to state the argument type `Canon Err`
  at all. This is the one place in this module where a direction of the
  equivalence needs strictly less than the headline finding.
- `canonEquiv : Grade Err ≃ Canon Err`, `canonEquiv_union`,
  `canonEquiv_bot` carry `Grade.join`/`Grade.bot` across to
  `Canon.union`/`Canon.ofFinset Grade.bot`. `Canon.union` is defined by
  round-tripping through `Finset` (sort, union, re-sort) rather than by a
  merge algorithm — **this is not the C++ algorithm**, which merges two
  already-sorted lists directly without revisiting either one's order;
  the round-trip is enough to prove `canonEquiv_union`, not a claim about
  how the C++ carrier is or should be implemented.
- `Canon.ofList`/`canon_perm`: `ofList` sorts a `List Err` via the
  union-of-singletons fold `joinAll` (`docs/design.md#traverse`'s Tuple
  subsection), so that `canon_perm : gs ~ gs' → ofList gs = ofList gs'` —
  **the direct statement of "`error_set<A,B>` is `error_set<B,A>`"** —
  can cite `joinAll_perm` rather than reproving order-independence from
  `List.Perm` directly.

> **`canon_requires_linear_order`.** Not a theorem — there is no false
> statement to refute, only a hypothesis to record. `Grade Err :=
> Finset Err` needs only `[DecidableEq Err]`: forming a *set* only ever
> needs to tell two elements apart. `Canon Err` needs strictly more,
> `[LinearOrder Err]` — a decidable *total* order — because sorting needs
> a definite answer for every pair of distinct elements, not just
> "different." In C++ terms: `Grade`'s `DecidableEq` is nominal typing,
> which C++ gets for free from the type system; `Canon`'s `LinearOrder`
> is a total order over *whatever the sorted detail carrier orders error
> types by* (a `<`-comparison on `std::type_index`, a fixed enumeration —
> the design never had to name it). Nothing before this step tested the
> canonicalization mechanism at all: `Finset`, used everywhere else in
> this model, is a quotient and is order-free by construction, so it
> never exercised the sorting the C++ alias actually performs. This gap
> — an abstract grade needing less than its C++ canonicalization
> mechanism does — is the finding this step exists to record.

**Mathlib names, re-checked at the pinned commit rather than guessed.**
This codebase's pinned Mathlib has replaced the historical
`List.Sorted r` (a `List.Pairwise`-based predicate taking an explicit
relation) with `List.SortedLE`/`SortedLT`/`SortedGE`/`SortedGT` (each
`StrictMono`/`Monotone` on `l.get`, fixed to `≤`/`<`/`≥`/`>`); the step
brief's `l.Sorted (· < ·)` does not exist at this commit; `Canon` uses
`List.SortedLT` instead. `Finset.sort_toFinset` and `List.toFinset` exist
under the names the step brief expected; `Finset.sort`'s default relation
argument was confirmed by reading `Mathlib/Data/Finset/Sort.lean` rather
than assumed.

## ungraded-baseline

**The question this section answers.** Every law recorded so far states
one number: which pomonoid property its *proof* needs. That number
conflates two different questions — what the law costs *at all* (true of
any monad/applicative/traversal, graded or not) and what grading adds *on
top*. This section is the second column, built by fixing a single grade
`g` and writing the same laws down again.

**The construction (`Graded/Ungraded.lean`).** `Fixed g α := Graded g α`
— not a new type, the existing carrier with the grade held still.
`pureF` reuses `fromEmpty` ([subsumption](#subsumption)) rather than
going through `Grade.bot`: a fixed-grade `pure` has nowhere else to land.
`bindF x f := cast (Grade.join_idem g) (bind x f)`, `apF`/`map2F`
likewise — each collapses the one `Grade.join g g` its underlying
operation produces back down to `g`. `traverse` needed no such wrapper:
[traverse-list] already built it uniform in one grade throughout, so
`Fixed`'s traversal *is* `Graded.traverse`, unchanged — confirmed, not
merely asserted; see below.

**The headline result.** `bindF_pure_left`, `bindF_pure_right`,
`bindF_assoc`, and the four `apF_*` laws are the ordinary monad and
applicative laws, verbatim — no `cast`, no `join`, nothing about grades
in any statement. Their *proofs* still cite `Grade.join_idem` throughout
(nothing is free), but never unit or associativity: `pureF` is already at
`g`, not at `⊥`, so `bind_pure_left`/`ap_pure_id`'s `Grade.bot_join` has
nothing left to transport, and `bindF_assoc`/`apF_comp` need no
`Grade.join_assoc` either, because every grade is already the same `g`
before any question of re-associating could arise.

### The two-column table: monad and applicative

| law | ungraded statement | what grading adds (proof only) |
|---|---|---|
| `bindF_pure_left` | `bindF (pureF a) f = f a` | `Grade.join_idem` (via `bindF_ok`) — `bind_pure_left`'s `Grade.bot_join` is gone entirely |
| `bindF_pure_right` | `bindF x pureF = x` | `Grade.join_idem` only — `bind_pure_right`'s `Grade.join_bot` is gone |
| `bindF_assoc` | `bindF (bindF x f) k = bindF x (fun a => bindF (f a) k)` | `Grade.join_idem` only, cited once per `bindF` via `bindF_ok`/`bindF_err` — `bind_assoc`'s `Grade.join_assoc` is gone: with every grade already `g`, the two reduction lemmas collapse both sides to the same term before any re-associating could be asked for |
| `apF_pure_id` | `apF (pureF id) x = x` | `Grade.join_idem` only — `ap_pure_id`'s `Grade.bot_join` is gone |
| `apF_pure_pure` | `apF (pureF f) (pureF a) = pureF (f a)` | `Grade.join_idem` only — `ap_pure_pure`'s `Grade.bot_join` (`∅ ∪ ∅ = ∅`) is gone |
| `apF_interchange` | `apF u (pureF a) = apF (pureF (fun f => f a)) u` | `Grade.join_idem` only — `ap_interchange`'s two separate unit lemmas are gone |
| `apF_comp` | `apF (apF (apF (pureF Function.comp) u) v) w = apF u (apF v w)` | `Grade.join_idem` only — `ap_comp`'s `Grade.bot_join` *and* `Grade.join_assoc` are both gone |

**Every general-law property in this table's "proof" column disappears
except idempotence**, and idempotence itself never appears in any
*statement* — only in the reduction lemmas (`bindF_ok`/`bindF_err`/
`apF_ok_ok`/`apF_err_left`/`apF_ok_err`) each law is built from. This is
the precise sense in which grading "costs nothing" for a single error
type: the unit and associativity properties `bind`/`ap`'s general laws
need are entirely a *multi-grade* phenomenon (they exist to reconcile
`∅`, `g`, `h`, `j` as genuinely different `Finset`s); collapse every
grade to one and they vanish, leaving only the one property — idempotence
— that a *single* grade can still fail to have (see
[grade-obligations](../tmp/plan/step-grade-obligations.md)).

**A finding not formalised as a theorem.** `ap_flip`'s "at most one side
is an error" hypothesis ([applicative](#applicative)) is **not a cost of
grading**. Its grade-level obstruction (`Grade.join_comm`, comparing
`Grade.join g h` against `Grade.join h g`) becomes, at a fixed grade, a
comparison of `Grade.join g g` against itself — trivial, no property
needed. But the *value*-level disagreement (which of two failing sides a
caller sees) is about evaluation order, not grades, and survives fully
intact at a fixed grade — it would hold just as unchanged for a plain
ungraded `Sum`/`Either`-shaped applicative combining two independently-
failing computations. Recorded here, not as `apFlippedF` (out of this
step's declared scope): the grade-level part of `ap_flip` really is a
grading cost, and the value-level part really is not, and the two halves
of that one law come apart cleanly once a grade is held fixed.

### traverse: unchanged, confirmed

`traverse` is defined uniform in one grade `g` throughout ([traverse](#traverse)),
so there is no separate `traverseF` to write and no separate row for what
grading "adds" to it: `Graded.traverse` already *is* its fixed-grade
form. `Tests/Ungraded.lean` confirms this is not merely a definitional
coincidence rather than checking anything: every `traverse` example in
`Tests/Traverse.lean` already runs at one grade, and the sole new fact
this step adds, `traverse_fromEmpty_map`, is a two-line corollary of
`traverse_map` and `traverse_fromEmpty`, both already in
`Graded/Traverse.lean`.

**The correspondence with `LawfulTraversable`** (`Mathlib.Control.Traversable.Basic`,
instantiated for `Sum σ` in `Mathlib.Control.Traversable.Instances`):

| Mathlib field | `Graded.Traverse` counterpart | note |
|---|---|---|
| `id_traverse : traverse (pure : α → Id α) x = pure x` | `traverse_fromEmpty : traverse (fromEmpty : α → Graded g α) xs = fromEmpty xs` | direct match — `Graded g` plays `Id`'s role, `fromEmpty` plays `pure`'s; both sides are the error-free embedding of the untouched list |
| `comp_traverse` | `traverseComp_eq` ([compose](#compose)'s `Comp` subsection, [compose-applicative]) | direct match, already established — see the composition rows below |
| `traverse_eq_map_id : traverse (pure ∘ f) x = pure (f <$> x)` | `traverse_fromEmpty_map : traverse (fromEmpty ∘ f) xs = fromEmpty (xs.map f)` (`Graded/Ungraded.lean`, this step) | direct match, added this step — not previously stated anywhere in `Graded/Traverse.lean` |
| `naturality` (for an `ApplicativeTransformation F G`) | **none** | **missing, Mathlib → ours.** This codebase has no notion of a transformation between two genuinely *different* applicatives; the closest analogue, `widen`, changes only the grade of the *same* functor `Graded`, never relates `Graded g` to an unrelated `F`. A finding, not a gap this step closes. |
| `traverse_length` (shape preservation, "the P3200 promise") | — | **missing, ours → Mathlib.** `LawfulTraversable`'s law set has no generic shape-preservation axiom; it is specific to `List`'s own instance, not part of the abstract class. |

### The three composition rows

The row [ungraded-baseline]'s own brief asked for, now that
[compose-applicative] has closed [graded-traversable-composition](#graded-traversable-composition):

| statement | grading | result |
|---|---|---|
| `flatten (map (traverse k) (traverse f xs)) = traverse (fun a => flatten (map k (f a))) xs`, `f`/`k` both at the *same* fixed grade `g` | ungraded (re-confirmed this step, `Tests/Ungraded.lean`, `fT`/`kT` at `gE = {E.parse, E.range}`) | **fails.** `flatten (map (traverse kT) (traverse fT [0,1]))` renders `"err E.parse"` (position 1's `fT` failure, the only one the left side ever consults); `traverse (fun a => flatten (map kT (fT a))) [0,1]` renders `"err E.range"` (position 0's `kT` failure, seen first by the right side's own left-to-right short circuit). Same disagreement [compose-flatten] found, confirmed to survive with the grade fixed — **therefore not a fact about grading**, exactly as [graded-traversable-composition](#graded-traversable-composition) already concluded from the general-grade re-run. |
| `Sum.comp_traverse` (Mathlib, `Sum σ`): `traverse (Comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))` | ungraded, Mathlib's own carrier | **holds**, unconditionally — Mathlib's own `LawfulTraversable (Sum σ)` instance, `Mathlib/Control/Traversable/Instances.lean`. Two layers kept apart by `Comp.mk`, never flattened. |
| `traverseComp_eq` (`Graded/ComposeApp.lean`, [compose-applicative]): `traverseComp (fun a => map k (f a)) xs = map (traverse k) (traverse f xs)` | graded, product form `Comp g h α := Graded g (Graded h α)` | **holds**, unconditionally — no `flatten`, both grades kept separate as `Comp`'s own indices instead of a wrapper. Recognisably the same law as `Sum.comp_traverse` above, transported. |

The pattern across all three: a composition law about two layers **kept
separate** holds, whether ungraded (`Sum.comp_traverse`) or graded
(`traverseComp_eq`); the same law with the layers **flattened first**
fails, whether ungraded or graded. Grading tracks which structure a
composition law is stated against; it does not change whether flattening
first is a sound move, because it never was.

### Wider pass: the other anchors

The two-column table above is complete for monad/applicative/traverse —
the laws this step's brief names as its focus. The remaining anchors
([carrier](#carrier), [subsumption](#subsumption), [compose](#compose),
[morphisms](#morphisms)) do not get comparably-shaped rows, for a
substantive reason each, not an oversight:

- **[carrier](#carrier)'s `map_id`/`map_comp`.** Grading adds nothing to
  either statement *or* proof: `map`'s type never mentions the grade
  (`Graded.map`'s docstring already says so — "functors are oblivious to
  grading, true by construction, not by proof"), so there is no fixed-
  grade specialization to write; the ungraded and graded forms are the
  same theorem.
- **[subsumption](#subsumption)'s `widen` family.** These laws are
  inherently *about* relating two different grades; "fix the grade" makes
  every `widen` an identity along `g ⊆ g` (already the content of
  `widen_refl`, free, no property). There is no meaningful second column
  for a law whose entire subject is grade change — collapsing the two
  grades to one collapses the law to a triviality already on record, not
  to a new fact.
- **[compose](#compose)'s `flatten` family.** Same shape as `widen`:
  `flatten : Graded g (Graded h α) → Graded (Grade.join g h) α` is about
  a *nested* pair of grades. At `g = h` the idem-collapse technique this
  step used for `bindF`/`apF` would apply identically — `flatten_flatten`
  would need `Grade.join_idem` where the general law needs
  `Grade.join_assoc`, mirroring `bindF_assoc`'s own finding exactly — but
  building a `flattenF` was not asked for by this step and is not built
  here (`Graded/Compose.lean` is out of its declared file scope).
- **[morphisms](#morphisms)'s `rename`.** `Grade.rename φ` is a
  transport *between* two grades (possibly two different `Err` types)
  along `φ`; at `φ := id` it is already the identity
  (`Finset.image id = id`), and a morphism law with only one grade to
  relate is not a morphism law at all. No second column applies.

### The Mathlib transport, bound to three attempts

**Landed within the bound — proved, not merely tabulated.** `Fixed g α`
is not literally Mathlib's `Sum Err α`: an `err` carries an `Err`
*together with* a proof of its membership in `g`, so the honest ungraded
counterpart is `Sum {e : Err // e ∈ g} α` (Mathlib's `σ` instantiated at
that subtype), matching `Mathlib.Control.Basic`'s `Monad (Sum e)` and
`Mathlib.Control.Traversable.Instances`'s `LawfulTraversable (Sum σ)`.
`Graded/Ungraded.lean`'s `sumEquiv : Fixed g α ≃ ({e : Err // e ∈ g} ⊕ α)`
is that `Equiv` — `toSum`/`ofSum`, each side `rfl` on every constructor,
the same style [carrier](#carrier)'s `emptyEquiv` already used one grade
earlier. `sumEquiv_pureF` and `sumEquiv_bindF` show `pureF`/`bindF`
correspond to `Sum`'s own `pure`/`Sum.bind` *as operations*, not merely as
matching types: transporting through `sumEquiv` before or after either
operation agrees.

**A finding in the Mathlib → ours direction, above `naturality`'s
already-noted absence.** `traverse_eq_map_id` had no stated counterpart
until this step added `traverse_fromEmpty_map` (see the traverse table
above) — the one place this step's "look for a missing row" instruction
actually turned one up and was cheap enough to close rather than merely
report.

**Log.**

- 2026-09-08 — [ungraded-baseline] built `Fixed`/`pureF`/`bindF`/`apF`/
  `map2F`, proved the ordinary monad and applicative laws cast-free in
  their statements, confirmed `traverse` needs no specialization, proved
  the `sumEquiv` transport to Mathlib's `Sum` (within the three-attempt
  bound), added `traverse_fromEmpty_map` as the one previously-missing
  Mathlib correspondence cheap enough to close, and re-confirmed the
  flattened composition law fails at a fixed grade — the row
  [graded-traversable-composition](#graded-traversable-composition)
  already predicted from the general-grade re-run, now checked
  executably rather than merely inferred.

## obligations

**Revised 2026-09-08 by [obligation-layering], superseding the account
this replaces in place — nothing below this note should be read as the
current shape of `Graded/Obligations.lean`; it is retained only where it
is still-accurate background (Mathlib classes considered, the `Nat`
demonstration, the non-commutative scope note).** [grade-obligations]
read the evidence available at the time as three layers, each "more
grade" than the last: a pomonoid carries the operational laws,
commutativity buys order-independence, idempotence buys
length-independence. [sufficient-grade-applicative] then produced a fact
that account cannot explain: `apK_flip`, the cast-free analogue of
`ap_flip`, needs **no** pomonoid property at all, where `ap_flip` needs
`Grade.join_comm` *by construction* — comparing `Grade.join g h` against
`Grade.join h g`, two different expressions for the same grade that only
exist because `ap`'s definition computes the union exactly. That is not a
missing case; it is a different account. [obligation-layering] classified
every theorem in the model that cites `join_comm`/`join_idem` against
this finding, and the three-layer story does not survive it: **no
operational law — monad, applicative, traversal, subsumption, or
morphism — needs either property.** Every consumer is a claim about a
grade's *spelling* (that two expressions denote the same grade, or that a
grade equals some fold), never about what an operation computes for a
payload or an error. The operational obligation on a grade is exactly
`Pomonoid`: associative, unital, ordered, monotone.

**The question this section answers.** `#cpp-counterpart` ends: "Only
`error_set` is intended as a grade for now; the design should not make it
the *only possible* grade." `Graded/Obligations.lean` turns the
observation into an obligation: Lean classes stating exactly what a grade
must supply for each law family, a proof that `Finset Err` satisfies all
of them (citing `Graded/Grade.lean`'s named lemmas, never reproving
them), and a commutative-but-not-idempotent counter-instance (`Nat`,
under `+`/`0`/`≤`) that fails exactly the theorems idempotence buys.

### The classification

For every theorem `docs/laws.md` tags `commutative` or `idempotent`
(mechanically, via `scripts/laws-inventory.py --by-property` — not
hand-copied from any step's prose: both [oracle-export] and
[grade-obligations] disagreed with their own generated tables at least
once), a verdict against what the proof actually does: **operational** —
a law about what `bind`/`ap`/`traverse`/`widen`/`rename` computes for a
payload or an error — or **canonicalization** — a claim that two
expressions denote the same grade, or that a grade equals some fold.

| theorem | module | property tag | verdict | why |
|---|---|---|---|---|
| `join_comm` | `Grade.lean` | (defining) | *neither* | the primitive axiom itself; not a consumer of it |
| `join_idem` | `Grade.lean` | (defining) | *neither* | the primitive axiom itself; not a consumer of it |
| `ap_flip` | `Applicative.lean` | commutative | canonicalization | `cast (Grade.join_comm h g)` reconciles `ap`'s grade `join g h` against `apFlipped`'s `join h g` — two spellings of one union. The *value* agreement (at most one side errs) is proved by case split alone; `apK_flip` (`Graded/Sufficient.lean`) proves the identical value fact at a common sufficient grade citing **zero** properties |
| `flatten_comm` | `Compose.lean` | commutative | canonicalization | same shape: `cast (Grade.join_comm h g)`. `Graded g (Graded h α)` has at most one error *by construction* (three inhabited shapes, never two errors at once), so which value survives never needed reconciling — only the two grade spellings did |
| `Comp.grade_reassoc` | `ComposeApp.lean` | associative, commutative | canonicalization | a pure `Grade`-level equation with no carrier in sight: reassociates `(g⊔h)⊔(g'⊔h')` into `(g⊔g')⊔(h⊔h')` |
| `Comp.traverseComp_cons` | `ComposeApp.lean` | idempotent | canonicalization — checked, not assumed | `Comp.castGH (Grade.join_idem g) (Grade.join_idem h)`. Traced through the tactic script: the value branch is a plain case split on `f x` and `Comp.traverseRaw f xs`'s shape, closed by `cast_ok`/`cast_err` alone — idempotence appears only in the statement's cast target, never inside the case split that picks the result |
| `foldGrade_cons_ne_nil` | `Traverse.lean` | idempotent, unit | canonicalization | the textbook case the hypothesis names: the theorem literally asserts a grade equals a fold |
| `traverse_cons` | `Traverse.lean` | idempotent | canonicalization — checked, not assumed | `cast (Grade.join_idem g)`; same case-split-then-`cast_ok`/`cast_err` shape as `Comp.traverseComp_cons` |
| `traverse_cons_err_left` | `Traverse.lean` | idempotent, order | canonicalization | `Grade.join_idem g ▸ …` transports a *membership proof* (`e ∈ g`) across the identity `join g g = g`; which error survives is already fixed by the hypothesis `hfx`, before idempotence is used at all |
| `traverse_cons_ok_err` | `Traverse.lean` | idempotent, order | canonicalization | the mirror of the row above, other side |
| `traverse_fromEmpty` | `Traverse.lean` | idempotent | canonicalization | delegates to `traverse_cons`'s cast; the payload (`y :: ys`) is already determined before the cast applies |
| `joinAll_perm` | `Tuple.lean` | associative, commutative | canonicalization | pure `Grade`-level: reorders a *static* list of element grades; no carrier value appears in the statement |
| `join_mem_eq` | `Tuple.lean` | associative, commutative, idempotent | canonicalization | pure `Grade`-level: `join g (joinAll gs) = joinAll gs` — a collapse of two spellings of the same grade |
| `foldG_cons_ne_nil` | `Obligations.lean` | idempotent, unit | canonicalization | the generic mirror of `foldGrade_cons_ne_nil`, same reading |
| `joinAllG_perm` | `Obligations.lean` | associative, commutative | canonicalization | the generic mirror of `joinAll_perm` |
| `join_le` | `Obligations.lean` | idempotent, order | grade-boundedness — see below | never mentions a carrier value, `bind`, `ap`, `traverse`, `widen`, or `rename`; a `Pomonoid` inequality, not an equality of two spellings either |
| `foldG_le` | `Obligations.lean` | order (mechanically — see below) | grade-boundedness, the sharpest case — see below | |

**No operational counterexample.** Every one of the fourteen non-defining
rows is a claim about the grade itself — that two ways of writing it
denote the same thing, that it equals some fold, or (the last two rows)
that it is bounded by something. None is a claim about what `bind`,
`ap`, `traverse`, `widen`, or `rename` computes for an actual payload or
error. The trap this step's brief set — that `Comp.traverseComp_cons`
and the `traverse_cons` family might secretly need idempotence *to choose
a value*, not merely to spell a grade — does not occur anywhere in the
table: every idempotence citation in a `traverse`-shaped theorem is spent
entirely inside a `cast`/`▸` target, never inside the case split that
determines the result.

### The sharpest case: `join_le` and `foldG_le`

These two do not fit the operational/canonicalization split cleanly,
because they are not about a carrier at all — `foldG : G → List α → G`
never touches a `Graded g α` value, only counts list length against an
abstract grade `G` — and `join_le`'s statement (`a ≤ c → b ≤ c → join a
b ≤ c`) is an inequality, not a claim that two spellings are equal.
"Bounded by `g`" sounds operational, because at the concrete level
`Graded.Traverse.foldGrade_le` genuinely is part of *defining*
`traverse` (see [traverse](#traverse)): the public `traverse` widens
along it, not along the exactness fact `foldGrade_cons_ne_nil`.

But `foldGrade_le` — the fact actually used to define `traverse` — needs
only order (`Grade.join_le`, `Grade.bot_le`), proved directly from
`Finset.union_subset`, no idempotence anywhere. The generic
`Obligations.foldG_le` needs `IsIdemPomonoid` only because
`Graded/Obligations.lean` deliberately declined to make `join_le` a
primitive `Pomonoid` field — doing so would foreclose the `Nat`
counter-instance this module exists to run, since `Nat`'s "join" (`+`) is
not a lattice join. With `join_le` non-primitive, the only generic route
back to boundedness is `join_mono` plus `join_idem`
(`join_mono ha hb : join a b ≤ join c c`, then `join_idem c` collapses
the right side to `c`) — so `foldG_le`'s idempotence dependency is an
artifact of which order fact `Obligations.lean` chose as primitive, not a
requirement of any traversal on values. At every concrete grade this
project has produced, the *real* operational fact (`foldGrade_le`) is
free of it.

**Verdict: grade-boundedness, not an operational counterexample** — but a
genuinely different kind of canonicalization claim than an equality of
spellings, and worth keeping distinct from the other fourteen rather than
folding it in silently. It is also the row that most directly bears on
[grade-join-strength](#grade-join-strength): see there for what it
settles and what it does not.

**A gap in the mechanical table, found while classifying this row.**
`docs/laws.md` tags `foldG_le` only `order`, not `idempotent`, even
though its Lean signature requires `[IsIdemPomonoid G]` and its proof
genuinely needs `join_idem` (by calling `join_le`, which needs it). This
is not a new parser bug: `scripts/laws-inventory.py`'s own docstring
already disclaims seeing through a delegated call ("it does not try to
see through a `simp only [someDef]` unfold to whatever property
`someDef`'s own body cites") — `foldG_le`'s proof text mentions `join_le`
by name, and `join_le` is tagged `order` in `ORDER_SUPPLEMENT`, so the
heuristic never looks inside `join_le`'s own body for the `join_idem`
there. The type signature, not the generated tag, is the ground truth
used for this row.

### The restructure

The three-class tower (`Pomonoid` → `IsCommPomonoid` → `IsIdemPomonoid`,
nested) becomes `Pomonoid` plus **three independent siblings**:

```
class Pomonoid (G : Type u) where            -- unchanged: the operational obligation
  join, bot, le, join_assoc, bot_join, join_bot, le_refl', le_trans', bot_le, join_mono

class IsCommPomonoid (G : Type u) extends Pomonoid G where
  join_comm : ∀ a b, join a b = join b a

class IsIdemPomonoid (G : Type u) extends Pomonoid G where   -- no longer extends IsCommPomonoid
  join_idem : ∀ a, join a a = a

class IsCanonicalPomonoid (G : Type u) extends Pomonoid G where
  join_comm : ∀ a b, join a b = join b a
  join_idem : ∀ a, join a a = a
```

`IsCommPomonoid` and `IsIdemPomonoid` no longer nest — the classification
above is *why*: `foldG_le`/`foldG_cons_ne_nil` cite `join_idem` alone,
`joinAllG_perm` cites `join_comm` alone, and nothing in this module (or
anywhere else — the three classes are used nowhere outside
`Graded/Obligations.lean` and `Tests/Obligations.lean`) ever needs both
at once. The old nesting was a real, if invisible, over-strong
hypothesis: `foldG_le`/`foldG_cons_ne_nil` took `IsIdemPomonoid`, which —
through `extends IsCommPomonoid` — silently required commutativity
neither proof ever cites, in tension with `docs/RULES.md`'s "a theorem
takes the weakest hypothesis that proves it." Decoupling fixes this
without touching either theorem's name or its conclusion.

`IsCanonicalPomonoid` bundles both axioms as its own direct fields (not
by extending both `IsCommPomonoid` and `IsIdemPomonoid`, which would
reintroduce a diamond back to `Pomonoid`). No theorem in
`Graded/Obligations.lean` takes it as a hypothesis, and that absence is
the point: it exists to *name* the bundle a real grade inhabits, not
because any internal proof needs the conjunction. `Grade Err` gets an
instance (`Finset` union is both commutative and idempotent); `Nat` does
not (it has `IsCommPomonoid` alone). Read against the classification
above, this is exactly the shape the hypothesis predicts:
`IsCanonicalPomonoid` names "this grade's *type* promises canonical exact
spelling" — order-independent and length-independent — as one name
instead of two, because that is what `error_set` promises in C++, not
because `and_then` or `apply` need it.

Every existing theorem in `Graded/Obligations.lean` remains provable
unchanged (`make all` GREEN before and after this restructure), and both
the `Grade`/`Finset` and `Nat` instances still resolve — `Nat` now
additionally fails to instantiate `IsCanonicalPomonoid`, for the same
reason it already failed `IsIdemPomonoid`.

### What changed from [grade-obligations], and why

| | [grade-obligations]'s account | this section, now |
|---|---|---|
| shape | three nested layers, each "more grade" | one operational class (`Pomonoid`) plus three independent mixins |
| what commutativity buys | order-independence, a genuine extra capability | reconciling two *spellings* of an exactly-computed union; no capability any operation needs |
| what idempotence buys | length-independence, a genuine extra capability | the same — reconciling `join g g` with `g`; no capability any operation needs, except the grade's own boundedness bookkeeping (`foldG_le`) |
| `foldG_le`/`foldG_cons_ne_nil`'s hypothesis | `IsIdemPomonoid` (which silently also required `IsCommPomonoid`) | `IsIdemPomonoid` (now idempotence alone, nothing silent) |
| `joinAllG_perm`'s hypothesis | `IsCommPomonoid` | unchanged |
| the paper's claim | "a grade needs three algebraic layers" | "`error_set` has to be a semilattice because of a promise its C++ *type* makes (canonical spelling), not because any operation on values needs it" |

[grade-obligations]'s measurements below (the `Nat` counter-instance, the
Mathlib-classes-considered survey, the non-commutative scope note) are
unaffected and retained as background; what changed is the
*interpretation* of why the layers exist, and the class shape now says so
directly.

### What was deliberately not copied from `Graded/Grade.lean`

`Graded.Grade.join_le` (`g ⊆ k → h ⊆ k → g ∪ h ⊆ k`, proved directly by
`Finset.union_subset`) and its two one-sided cousins `le_join_left`/
`le_join_right` are **not** primitive `Pomonoid` fields here, and this is
itself a finding, not a simplification of convenience.

`join_le` is a least-upper-bound fact: it holds for `Finset` union because
union genuinely *is* a semilattice join relative to `⊆`. It is **not**
implied by "associative, unital, ordered, monotone" — the `Nat`
counter-instance below satisfies every other field (`join_assoc`,
`bot_join`/`join_bot`, `le_refl'`/`le_trans'`, `bot_le`, `join_mono`,
`join_comm`) and still refutes it: `1 ≤ 1` twice over, but `1 + 1 ≰ 1`.
Making `join_le` a required `Pomonoid` field would make `Nat` unable to
instantiate even the base layer, foreclosing the demonstration this
section exists to run. `le_join_left`/`le_join_right`, by contrast, *are*
derivable from the fields kept (`join_mono`, `join_bot`/`bot_join`,
`bot_le` — the same style as `join_mono (le_refl' a) (bot_le b)` rewritten
along `join_bot`) and are restated in `Graded/Obligations.lean` as
theorems, not fields, so the vocabulary still lines up with
`Graded/Grade.lean`.

### Mathlib classes considered, and why none were inherited from

Checked against the pinned Mathlib before writing `Pomonoid` fresh:

- **`SemilatticeSup`** (`Mathlib.Order.Lattice`) — a `PartialOrder` plus a
  `sup` that *is* the least upper bound (`SemilatticeSup`'s own `le_sup_left`/
  `le_sup_right`/`sup_le` are exactly `Grade`'s `le_join_left`/
  `le_join_right`/`join_le`). This is the closest match to what `Grade`
  actually is — and precisely the reason it does not fit `Nat`: `Nat`
  under `+` is not a `SemilatticeSup` (`sup_le` fails, per the finding
  above), so inheriting from it would have made the `Nat` counter-instance
  impossible to state at all.
- **`IsOrderedAddMonoid`/`IsOrderedCancelAddMonoid`**
  (`Mathlib.Algebra.Order.Monoid.Defs`) — mixin classes layered on top of
  `AddCommMonoid`/`Preorder`, requiring only monotonicity
  (`add_le_add_left`), not a least-upper-bound property. This is the
  actual shape `Pomonoid` ended up with — but inheriting it would still
  pull in Mathlib's `AddCommMonoid`/`Preorder` hierarchy and its `simp`
  set, which is exactly what [grade](#grade)'s own provisional note
  already declined for `Grade`, for the same reason: an inherited instance
  lets later `simp` calls reach for these properties invisibly, defeating
  the point of a name-by-name grep. `Pomonoid` is written multiplicatively
  and fresh instead, so `join_mono` (this project's name) stays the
  citation, not `add_le_add_left` (Mathlib's).
- **`CovariantClass`** (`Mathlib.Algebra.Order.Monoid.Unbundled.Defs`) — the
  mixin `IsOrderedAddMonoid` itself is stated in terms of; same reasoning
  applies one level down.

The project's existing decision at [grade](#grade) — keep `Grade` off
Mathlib's lattice classes so lemma use stays greppable — extends cleanly
to this abstract layer: it was checked, not assumed, and the same
conclusion holds for the same reason, plus the sharper reason above (the
closest fit, `SemilatticeSup`, is actually *too strong* to admit the `Nat`
counter-instance at all).

### The `Nat` demonstration

`instance : Pomonoid Nat` (`join := (· + ·)`, `bot := 0`, `le := (· ≤
·)`, citing `Nat.add_assoc`/`Nat.zero_add`/`Nat.add_zero`/`Nat.le_refl`/
`Nat.le_trans`/`Nat.zero_le`/`Nat.add_le_add`) and `instance :
IsCommPomonoid Nat` (`Nat.add_comm`) — no `IsIdemPomonoid Nat` instance
exists, and `nat_not_idem : ¬ ∀ a : Nat, a + a = a` proves why
(`1 + 1 = 2 ≠ 1`).

Executable, adjacent, `Grade` then `Nat`:

```
#guard foldG ({E.parse} : Grade E) [(), (), ()] = {E.parse}   -- idempotent: stays put
#guard foldG (1 : Nat) [(), (), ()] = 3                        -- not idempotent: grows
```

Two disproofs at `Nat`, both from the same witness (`g := 1`, `xs := [(),
(), ()]`):

- `foldG_cons_ne_nil` fails: `¬ ∀ g xs, xs ≠ [] → foldG g xs = g` (the
  length-independence claim — the theorem [traverse](#traverse)'s
  `foldGrade_cons_ne_nil` needed idempotence for, now shown false without
  it).
- `foldG_le` fails too: `¬ ∀ g xs, foldG g xs ≤ g` (the boundedness claim
  — see "[The sharpest case](#obligations)" above for why this one is not
  free generically even though its concrete sibling `foldGrade_le` is).

And order-independence survives regardless: `joinAllG_perm` holds at
`Nat` (`joinAllG [1,2,3] = joinAllG [3,1,2] = 6`, by `IsCommPomonoid`
alone) exactly as it does at `Grade`. Put side by side, the `Nat` instance
shows the two axioms buying genuinely different things: commutativity
survives on its own; idempotence's absence breaks both of `foldG`'s
claims about a non-empty list.

### Judgement call, resolved

[grade-obligations] chose to nest `IsIdemPomonoid` under `IsCommPomonoid`
rather than sit it beside `Pomonoid`, provisionally, on the evidence that
neither headline theorem needing idempotence ever cites `join_comm`.
[obligation-layering] resolved it the other way: sit beside. The evidence
did not change; the reading of it did — "costs nothing observable" is an
argument for decoupling, not against it, once the goal is each theorem's
*weakest* hypothesis rather than "one class fewer." See
[The restructure](#obligations) above.

### Scope note: the optional non-commutative instance

Not included. A quick check of the free monoid (`List X` under `++`,
`[]`, ordered by `<+:` prefix) shows `join_mono` itself fails there in
general — `[1] <+: [1, 9]` and `[2] <+: [2]`, but `[1] ++ [2] = [1, 2]` is
not a prefix of `[1, 9] ++ [2] = [1, 9, 2]` — so it does not even reach
`Pomonoid`, let alone serve as a non-commutative counter-instance to
`joinAllG_perm`. Building a genuine non-commutative `Pomonoid` instance
would need a different carrier than the one this step's brief suggested,
which is more than "lands quickly" allows. The commutative layer's
necessity (`joinAllG_perm`'s dependence on `IsCommPomonoid`) is therefore
argued — via the layer-to-law table and the `Grade`/`Nat` agreement above
— but not demonstrated by a instance where it actually fails.

### grade-join-strength

**Question, as originally asked.** How strong is the obligation on a
grade's `join`: must it be a *least upper bound* for the order (a
join-semilattice, which is what `error_set`'s union is and what
[grade](#grade) calls it throughout), or merely an associative, unital,
monotone operation (an ordered monoid)?

**Status: OPEN, reframed by [obligation-layering] — sharpened, not
closed.** Raised by the orchestrator after [grade-obligations], which had
to choose and chose the weaker reading; reframed after
[obligation-layering]'s classification (`#obligations`) found that no
*operational* law (monad, applicative, traversal, subsumption, morphism)
ever needs `join_comm`/`join_idem`/`join_le` — every consumer is a claim
about a grade's spelling or bound, never about a value. That does not
answer the original question; it changes what answering it would mean.

**The reframing.** The question is no longer "does the algebra force
idempotence" (settled: it does not, `Nat` is the witness) but "must a
grade's C++ *type* promise canonical exact spelling — order-independent
and length-independent, i.e. genuinely be a join-semilattice — for
`traverse`'s signature to be writable at all?" [obligation-layering]'s
[#obligations](#obligations) section, "The sharpest case: `join_le` and
`foldG_le`", is the sharpest evidence either way:

- At the concrete `Grade` instance, `traverse`'s own definition
  (`Graded.Traverse.foldGrade_le`) costs *only* order — `Finset` union
  already is a semilattice join, so boundedness is free, and the
  idempotence `foldGrade_cons_ne_nil` costs is spent entirely on the
  *exactness* claim, never the definition.
- Generically, over an abstract `Pomonoid` that is *not* assumed to be a
  semilattice, even the *definition*-level boundedness fact (`foldG_le`)
  needs idempotence to reconstruct — because `Graded/Obligations.lean`
  deliberately excludes `join_le` as a primitive (to keep `Nat` an
  instance).

Both readings therefore agree that **something in the grade's own
algebra** must supply boundedness before `traverse` can exist at a fixed
signature — either handed for free (grade = join-semilattice) or bought
with idempotence (grade = ordered monoid, idempotence as a separate
axiom). Where they disagree is only in *how* that requirement enters:
as part of what a grade already *is* (the stronger reading), or as an
extra, independently statable axiom (the weaker reading, `Graded/
Obligations.lean`'s current shape). Since `join_le` plus antisymmetry
already implies `join_idem` (below), the two readings are not two
different sets of admissible grades so much as two different ways of
*naming* the one requirement traversal has.

> **`join_le` together with antisymmetry of the order implies
> `join_idem`.** Verified in Lean: `join_le le_refl' le_refl'` gives
> `join a a ≤ a`, `join_mono le_refl' (bot_le a)` rewritten by `join_bot`
> gives `a ≤ join a a`, and antisymmetry closes it. Both concrete grades
> in this model (`Finset` under `⊆`, `Nat` under `≤`) have antisymmetric
> orders; `Pomonoid` simply does not require it as a field, so `le` there
> is really a preorder.

**What each answer still costs, restated against the classification.**

- *Grade = join-semilattice.* Boundedness and length-independence are
  free, `Nat` under `+` is simply not a grade, and the type itself
  guarantees `traverse` is always writable. The paper's obligation on a
  grade is short, strong, and — per this step's classification —
  entirely about what the *type* promises, never about what `and_then`
  or `apply` need.
- *Grade = ordered monoid.* Idempotence is a real, separately-stated
  extra requirement; `Nat`-style counting grades are admissible as
  grades in every other respect (they get a working `bind`/`ap`, cast-
  laden but total, per [sufficient-grade-bind]/[sufficient-grade-
  applicative]) but cannot support `traverse`. This is `Graded/
  Obligations.lean`'s current shape.

**What is settled now, that was not before.** Commutativity is
independent of both readings and is needed nowhere operationally — every
citation in the classification table is canonicalization. Boundedness
and length-independence are needed only for `traverse`'s own bookkeeping,
never for `bind`, `ap`, subsumption, or morphisms — so whichever way this
question is decided, it constrains only what `traverse` requires of a
grade, not what a P3200 grade must be to support `and_then`/`apply` at
all.

**What is not settled, and what would settle it.** Whether P3200's grade
*concept* should require the stronger promise (a real join-semilattice)
or permit the weaker one (an ordered monoid, with `traverse` simply
absent for grades that do not also happen to be idempotent) is a decision
about what a grade should be allowed to be, not a fact the code can
determine — [obligation-layering]'s classification narrows the stakes
(only `traverse` is at issue) without forcing an answer. It would be
settled by either: (a) an explicit P3200 design decision that `traverse`
is only ever offered for `error_set`-like grades and non-lattice grades
simply do not get it (making the weaker reading fully adequate and this
question moot), or (b) a genuine non-lattice `Pomonoid` instance with a
real use for `traverse` that the current model cannot express, which
would argue for the stronger requirement. Neither exists yet; the `Nat`
instance is a demonstration, not a use case anyone wants `traverse` on.

**Log.**

- 2026-09-08 — [grade-obligations] excluded `join_le` from `Pomonoid` to
  keep the `Nat` instance, and found that `foldG_le` then needs
  idempotence generically though the concrete `Grade.join_le` proof does
  not.
- 2026-09-08 — orchestrator verified in Lean that `join_le` plus
  antisymmetry proves `join_idem`, so the exclusion is what makes
  idempotence look like an independent axiom. Question opened.
- 2026-09-08 — [obligation-layering] classified every `join_comm`/
  `join_idem` consumer in the model and found none operational, which
  reframes this question from "does the algebra force idempotence" to
  "must a grade's type promise canonical spelling for `traverse` to
  exist" — narrower, but not settled by the classification alone. See
  `#obligations`'s "the sharpest case" for the evidence.

### cast-burden-migration-scope

**Question.** How much of the model should gain a sufficient-grade,
cast-free layer: only `bind` and `ap`, or also `traverse`, `flatten`,
`Comp` and `GradedHom`?

**Status: OPEN**, and deliberately not planned yet.

**Why it is not planned yet.** A brief for the remaining four structures
written now would be guesswork, and this project already paid for exactly
that once: [compose-flatten]'s brief named the right structure in its
first sentence and then set the task against a different one, producing a
true refutation of a question nobody had asked
([graded-traversable-composition](#graded-traversable-composition)). The
brief for this must be written from [sufficient-grade-bind]'s and
[sufficient-grade-applicative]'s *measurements*, not from the expectation
that the pattern generalizes.

**What is already settled.** The shape of the fix is two layers and a
bridge, not a replacement, because the casts faithfully record that the
C++ `bind` computes the union grade
([cpp-counterpart](#cpp-counterpart)). Verified before planning:
`bind x f = bindK (le_join_left g h) (le_join_right g h) x f` closes by
`rfl` in both constructor cases, so the layers coexist definitionally and
no existing theorem has to change. The three monad laws state with no
`cast` at all in the sufficient-grade form.

**The measured burden, as of the integration review.** 39 of 146 theorems
carry a `cast` in their statement (26%). By module: `Monad` 7/8,
`Accum` 7/16, `ComposeApp` 6/13, `Morphism` 5/15, `Applicative` 5/11,
`Compose` 4/8, `Traverse` 2/12, `Carrier` 2/5, `Widen` 1/6, and
`Ungraded` **0/16** — at one fixed grade they vanish, which is what shows
the burden is a grade-arithmetic cost rather than an inherent one.

**What would decide it.** Whether the threaded `g ⊆ k` obligations stay
free at call sites. They are proof-irrelevant, so they should; if they do
not, the sufficient-grade layer trades casts in statements for proof
arguments at every use and is not worth extending. `GradedHom` is the
sharpest case: its *fields* are cast-quantified, so it is either the
biggest win or the place the design breaks.

**A finding to watch for, which would change more than the casts.**
`ap_flip` needs `join_comm` by construction, comparing `join g h` against
`join h g`. At a common `k` there is nothing to compare. If its analogue
needs no commutativity, then commutativity was a cost of computing the
grade *exactly* rather than a requirement of the applicative — which
revises [grade-obligations]' layering, where commutativity is currently
attributed to order-independence, and revises what P3200 must promise
about `error_set`.

**Log.**

- 2026-09-08 — integration review found the cast burden had outgrown
  [monad-laws]'s "tolerable, not dominating" verdict, and recommended
  bind-at-sufficient-grade as a follow-up run.
- 2026-09-08 — orchestrator verified the bridge theorem and the cast-free
  law statements before planning, and rejected the provisional note's
  "replace `bind`" reading as modelling a design P3200 does not have.
  [sufficient-grade-bind] and [sufficient-grade-applicative] planned; the
  remaining four structures left to this question.

## laws-inventory

The table: [`docs/laws.md`](laws.md) (146 theorems, generated from
`Graded/*.lean` by `scripts/laws-inventory.py`; the same data as
[`docs/laws.json`](laws.json)). `make laws` regenerates and diffs it, so it
cannot drift from the proofs; run it again after touching any
`Graded/*.lean` file. The probe list for the C++ side is
[`docs/probe-harness.md`](probe-harness.md): one equation per row that has
a C++ law, against [cpp-counterpart](#cpp-counterpart)'s names.

The verdicts below are written from that table, not from the plan's
prediction of it. Where the two disagree, the table wins — this step's own
brief predicted three things that turned out wrong in specifics (the
commutativity list, the idempotence-hypothesis count, and which modules
would show up at all), and each disagreement is recorded below rather than
silently corrected.

**Unit and associativity, no more: the monad and most of the applicative.**
`bind_pure_left`/`bind_pure_right` (unit), `bind_assoc` (associative),
`bind_map` (unit) — [monad](#monad)'s five laws never cite `join_comm`.
Every four-law applicative instance built the same way — `ap_pure_id`,
`ap_pure_pure`, `ap_interchange` (unit only) and `ap_comp` (unit +
associative) — repeats verbatim in `Graded/Applicative.lean`,
`Graded/Accum.lean`, and `Graded/ComposeApp.lean`'s `Comp.ap_*`: three
independent carriers (single-error, accumulating, nested-composite), the
same two properties, never commutativity. `Graded/Ungraded.lean`'s
fixed-grade mirrors (`bindF_pure_left`/`bindF_pure_right`/`bindF_assoc`,
`apF_pure_id`/`apF_pure_pure`/`apF_interchange`/`apF_comp`) spend no unit
or associativity at all — holding the grade fixed removes exactly the `∅`
and the reparenthesizing these properties paid for — and the table's
mechanical scan of their own proof text shows *no* property at all, not
even idempotence, because each one's own proof only pattern-matches into
an already-tabulated reduction lemma (`apF_ok_ok` and kin); the idempotence
these laws genuinely rest on is spent one level down, inside `bindF`/`apF`
*themselves*, which are `def`s and so never appear as rows at all. This is
the sharpest illustration in the table of the scan's own limit: a `def`
that bakes a property into a cast is invisible to a script that only reads
`theorem`s.

**Commutativity: six sites, not three.** The step brief predicted
`ap_flip`, `joinAll_perm`, `flatten_comm`. The table shows six (seven
counting the generic layer): `ap_flip` (`Graded/Applicative.lean`,
comparing `ap`'s grade `g ⊔ h` against `apFlipped`'s `h ⊔ g`);
`flatten_comm` (`Graded/Compose.lean`, comparing `flatten`'s grade against
`flatten`-after-`swap`'s); `Graded/Tuple.lean`'s `joinAll_perm` **and**
`join_mem_eq` — two sites in that module, not one, since `join_mem_eq` is
`joinAll_dedup`'s own load-bearing helper and cites `join_comm` directly
in its own right, not merely by inheriting from `joinAll_perm`; and
`Graded/ComposeApp.lean`'s `Comp.grade_reassoc`, which `flatten_ap` needs
to reassociate `(g ⊔ h) ⊔ (g' ⊔ h')` into `(g ⊔ g') ⊔ (h ⊔ h')`, cited
directly in `grade_reassoc`'s own proof and not in `flatten_ap`'s (see the
mechanical scan's own miss on this, below). `Graded/Obligations.lean`'s generic
`joinAllG_perm` is a seventh, separate confirmation at the abstract
`IsCommPomonoid` layer, matching `joinAll_perm` exactly — not a fourth
concrete site, since it proves the same fact again over an abstract
`[IsCommPomonoid G]` rather than depending on `joinAll_perm`.

**Idempotence: nine sites**, matching the table's `idempotent` column
after excluding `Grade.join_idem` itself (a property's own definition does
not depend on itself): `Graded/Traverse.lean`'s `foldGrade_cons_ne_nil`,
`traverse_cons`, `traverse_cons_err_left`, `traverse_cons_ok_err`,
`traverse_fromEmpty`; `Graded/Tuple.lean`'s `join_mem_eq` (also
commutative, above); `Graded/ComposeApp.lean`'s `Comp.traverseComp_cons`;
and `Graded/Obligations.lean`'s generic `foldG_cons_ne_nil` and `join_le`.
`Graded/Ungraded.lean`'s fixed-grade laws spend idempotence too, per that
module's own docstrings, but — as above — invisibly to the mechanical
scan, inside `bindF`/`apF`'s definitions rather than in any theorem's own
proof text.

**Order alone: `widen_refl`, `widen_widen`, `bind_widen`,
`flatten_widen_outer`/`flatten_widen_inner`, and both `foldGrade_le`s.**
Not every `widen_*` theorem needs it — `widen_map` and `widen_cast` need
no property at all, since mapping or casting alongside a widen never puts
two grades in a `join` together — only the two that relate two different
widenings (`widen_refl` via `le_refl'`, `widen_widen` via `le_trans'`) do.
`Graded/Traverse.lean`'s concrete `foldGrade_le` needs only the order,
exactly as predicted, via `Grade.join_le`/`Grade.bot_le`/`Grade.le_refl'`.
Its generic sibling in `Graded/Obligations.lean`, `foldG_le`, is where the
table's mechanical properties column is honestly incomplete rather than
wrong: its own proof text mentions only order tokens (`bot_le`,
`le_refl'`, the generic `join_le`), so the table shows `order` — but
[obligations](#obligations) already recorded that this `join_le` is
*itself* only provable from `join_mono` **and** `join_idem` together, once
a grade's `join_le` is not assumed as a primitive. So `foldG_le` genuinely
needs `IsIdemPomonoid`, not bare `Pomonoid`; the table shows what its
proof text cites, not what its type class hypothesis is, and the two
diverge exactly here. Read [#obligations](#obligations)'s own
layer-to-law table for the accurate version; don't take this table's
`order` tag for `foldG_le` as contradicting it.

**The at-most-one-error condition: four sites, not three, and it is not
the same finding four times.**

- `ap_flip` (`Graded/Applicative.lean`): the hypothesis `(∃ f', f =
  .ok f') ∨ (∃ a, x = .ok a)` is load-bearing — without it `ap` and
  `apFlipped` disagree on *which* error survives, only on the grade do
  they always agree (via `join_comm`).
- `Graded/Accum.lean`'s `toGraded_grade` states the *same* hypothesis,
  by design, to match `ap_flip` — but it turned out **not** to be needed:
  `toGraded_grade'` proves the unconditional form. `Accum.ap`'s
  concatenation puts the function's errors first, and `Graded.ap` always
  keeps the function's error when the function fails, so "first element
  of the accumulated list" and "the error `Graded.ap` keeps" coincide by
  construction, not by luck, on every input, not just the one-sided ones.
- `flatten_comm` (`Graded/Compose.lean`) needs **no** hypothesis at all.
  `ap`/`apFlipped` combine two *independent* values, each of which can
  independently fail; `flatten`'s nested carrier is a single value with
  exactly three inhabited shapes and can never hold two errors at once,
  so the condition that mattered for `ap_flip`/`toGraded_grade` is
  vacuously true here and never needs writing down.
- `flatten_ap` (`Graded/ComposeApp.lean`) needs a **different**,
  three-way disjunctive hypothesis discovered during its own proof:
  `ff`'s outer layer fails, *or* `ff` succeeds all the way through
  (outer *and* inner), *or* `xx`'s outer layer succeeds. This is not a
  restatement of `ap_flip`'s condition — it rules out the one case where
  `Comp.ap`'s short-circuit order (outer error, then outer error, then
  `ff`'s *inner* error, then `xx`'s) disagrees with flatten-then-`ap`'s
  (which surfaces `ff`'s inner error immediately). `flatten_ap` is also
  where the mechanical scan itself found nothing to cite: its own proof
  text names no property at all, because the grade equation it needs
  (`Comp.grade_reassoc`, associative + commutative) is cited by name as a
  cast target rather than re-derived — a real, load-bearing theorem the
  dumb heuristic cannot see through. See "What the checker refused" in
  [blog/letters/oracle-export.org](../blog/letters/oracle-export.org).

**What a different grade pomonoid must supply.** [#obligations](#obligations)
already names this precisely — `Pomonoid`, `IsCommPomonoid extends
Pomonoid`, `IsIdemPomonoid extends IsCommPomonoid` — and this table's
"unit/associative", "commutative", "idempotent" columns line up with that
hierarchy's three layers by construction. But which layer a given row
*actually* needs is now an open question, not a closed one:
[grade-join-strength](#grade-join-strength) (OPEN) asks whether a grade's
`join` must be a least upper bound. Under the stronger reading, `join_le`
(this table's `order` tag) plus antisymmetry *proves* `join_idem`, so
every row this document calls "idempotent" — the nine sites above — would
be a theorem rather than an independent axiom, and a future grade
satisfying the stronger reading gets `foldGrade_cons_ne_nil`,
`traverse_cons`, and the rest for free. This document does not answer
that question; it only notes that the "idempotent" column's *meaning*
depends on it.

## blog-series

Addressee: **"Steve,"**, signed **"--SMD"**. The letters are notes
addressed to the author, not to a third party; the reader they are *written
for* is unchanged — a working C++ programmer who has never opened Lean —
but the second person in them is the author himself. Decided 2026-09-08 by
the author, in an editorial pass (commit `e1fa465`) which also replaced
em-dashes with colons, parentheses or full stops. That pass covered the
**ten** letters that existed when it was made, which was every letter at
the time; the six written afterwards ([graded-morphism],
[canonical-representation], [compose-applicative], [ungraded-baseline],
[grade-obligations], [oracle-export]) were drafted from the older template
and were brought into the decided register by [blog-series-edit]. An
earlier revision of this paragraph said the pass covered all sixteen,
which it could not have. That pass is the register for the series; later letters
should match it rather than the earlier "Dear colleague" / "— Steve" form.

Letters directory: `blog/letters/`, one `<slug>.org` per step, per the
template in `docs/RULES.md#letter-template`.

**Ordering, numbering, and index: decided by [blog-series-edit].** Letters
0-15 run in checklist order (`baseline-capture` = Letter 0 through
`oracle-export` = Letter 15); `blog/letters/closing.org` is Letter 16.
Several letters from `monad-laws` (checklist step 5) onward had
self-numbered one higher than this (matching their raw checklist step
number rather than the step number minus one that `baseline-capture`'s
own "Letter 0" already implied); [blog-series-edit] corrected all of them
to the consistent, gap-free sequence. Every letter carries `#+SERIES_PREV`
/ `#+SERIES_NEXT` by slug. The reading index is
[`blog/letters/index.org`](../blog/letters/index.org).

**Decided, no longer provisional.** The placeholder "Dear colleague" was
replaced by the author on 2026-09-08; [blog-series-edit] must preserve
"Steve," / "--SMD" and must not reapply the placeholder from this anchor's
earlier text.

## provisional-decisions

Index of every `> **Provisional.**` mark in this document, by anchor:

- [#toolchain](#toolchain) — build-time numbers are machine- and
  network-dependent.
- [#grade](#grade) — no Mathlib lattice instance is *declared* for
  `Grade`; note the correction there, since the original rationale
  claimed a protection an `abbrev` cannot give.
- [#monad](#cast-burden-migration-scope) — **OPEN question**
  `cast-burden-migration-scope`: how much of the model gains a cast-free
  sufficient-grade layer. Deliberately unplanned until the first two
  steps' measurements exist.
- [#obligations](#grade-join-strength) — **OPEN question**
  `grade-join-strength`: whether a grade's join must be a least upper
  bound. Under the stronger reading `join_idem` is a theorem, not an
  axiom, and the three-layer account applies only to the weaker one.
- [#compose](#graded-traversable-composition) — **CLOSED**
  `graded-traversable-composition`: the flattened composition law is
  false (and the refutation is not about grading); the product-graded
  form `traverseComp_eq` holds unconditionally, built and proved by
  [compose-applicative]. Kept in this index because the anchor still
  carries the reasoning, not because anything is open.
- [#carrier](#carrier) — laws stated with exact union grades and `cast`,
  rather than `bind` at any sufficient grade.
- [#applicative](#applicative) — `Accum`'s error field is a `List Err`
  with a non-emptiness proof, not a `Multiset`.
- [#morphisms](#morphisms) — `GradedHom` requires neither injectivity nor
  surjectivity of the grade map; revisit only if a consumer needs to
  recover the source grade or needs every target grade hit.
