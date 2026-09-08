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

> **Provisional.** `Grade` is deliberately *not* registered as a Mathlib
> `SemilatticeSup`/`OrderedCommMonoid` instance, so that lemma use stays
> greppable: an instance would let `simp` reach for these properties
> invisibly, which defeats the point of naming them. Revisit if a later
> step needs Mathlib's lattice API for a proof that is otherwise long.

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
> [#monad](#monad) for the detail. Standing, not revisited.

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
dominating. Three small generic transport lemmas — `cast_ok`, `cast_err`,
`cast_widen` (the mirror of `Widen.widen_cast`), each one `subst e; rfl`
— handled every occurrence of `cast` meeting a constructor or a `widen`
across all five theorems; no proof needed more than that plus `cases` on
the scrutinee(s) and one closing `rw`. Rough count: of the ~45 lines of
proof text, perhaps a third is `cast`/`widen`-shuffling (the `change`
statements that spell out the fully-reduced goal) and the rest is
ordinary case analysis. Nothing here suggests revisiting the provisional
decision.

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

Filled by [traverse-list](../tmp/plan/step-traverse-list.md) and
[traverse-tuple](../tmp/plan/step-traverse-tuple.md).

## compose

Filled by [compose-flatten](../tmp/plan/step-compose-flatten.md).

## morphisms

Filled by [graded-morphism](../tmp/plan/step-graded-morphism.md).

## representation

Filled by [canonical-representation](../tmp/plan/step-canonical-representation.md).

## laws-inventory

Filled by [oracle-export](../tmp/plan/step-oracle-export.md).

## blog-series

Addressee: "Dear colleague" (a working C++ programmer who has never opened
Lean).

Letters directory: `blog/letters/`, one `<slug>.org` per step, per the
template in `docs/RULES.md#letter-template`.

Ordering and index: not decided here. [blog-series-edit] assembles the
reading order and the index page from the letters this plan produces; this
step writes only letter 0 (`blog/letters/baseline-capture.org`).

> **Provisional.** The addressee name "Dear colleague" is a placeholder.
> Revisit when [blog-series-edit] picks a final voice for the series, or
> sooner if a letter reads awkwardly addressed this way.

## provisional-decisions

Index of every `> **Provisional.**` mark in this document, by anchor:

- [#toolchain](#toolchain) — build-time numbers are machine- and
  network-dependent.
- [#blog-series](#blog-series) — addressee name "Dear colleague".
- [#carrier](#carrier) — laws stated with exact union grades and `cast`,
  rather than `bind` at any sufficient grade.
- [#applicative](#applicative) — `Accum`'s error field is a `List Err`
  with a non-emptiness proof, not a `Multiset`.
