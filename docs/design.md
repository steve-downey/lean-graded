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
`(g ⊔ h) ⊔ (g' ⊔ h')` into `(g ⊔ g') ⊔ (h ⊔ h')` — the second appearance
of `join_comm` in the whole model, after `ap_flip`. The *value* side fails
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
needs both `Grade.join_assoc` and `Grade.join_comm` — the second
appearance of `join_comm` in the whole model, after `ap_flip` — and the
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
- [#compose](#graded-traversable-composition) — **OPEN question**
  `graded-traversable-composition`: the classical Traversable composition
  law is refuted for the flattened carrier (and the refutation is not
  about grading); whether a `Compose`-aware version is worth building is
  undecided.
- [#carrier](#carrier) — laws stated with exact union grades and `cast`,
  rather than `bind` at any sufficient grade.
- [#applicative](#applicative) — `Accum`'s error field is a `List Err`
  with a non-emptiness proof, not a `Multiset`.
- [#morphisms](#morphisms) — `GradedHom` requires neither injectivity nor
  surjectivity of the grade map; revisit only if a consumer needs to
  recover the source grade or needs every target grade hit.
