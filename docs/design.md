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
