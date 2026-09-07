# Coordination worklist — 2026-09-07

Backlog from the typeclass-relationships design discussion held
2026-09-07 (deriving full instances from Monad, monoid canonicity,
structural conformance). Directions ratified by Steve in that
discussion; **all items are HELD pending further discussion — none are
scheduled for immediate execution**. Item 3 in particular is recorded so
it is not forgotten, not because it is next.

## 1. Named monoids; no numeric defaults

Decision: induced and numeric monoids are **named and available, but
not registered** as the default for a raw carrier. A carrier gets a
default `Monoid<T>` registration only where one instance is canonical
(string/vector concatenation stay; `Count` stays). Where no instance is
so right that any can be the default — numbers, booleans — the choice
is spelled by choosing a named carrier type.

- Provide the basic monoids for numbers and booleans as public named
  carriers in `monoid.hpp`: `Sum<T>`, `Product<T>`, `Max<T>`, `Min<T>`,
  `Any`, `All` (promoting `detail::Any`/`detail::All` out of
  `fold.hpp`), each registered on its own name, `DualMonoid`-style.
- `Max<T>`/`Min<T>` identities are the saturating values of `T`
  (`numeric_limits<T>::lowest()` / `::max()`; the infinities where the
  type has them). No adjoined-identity `T+1` element type.
- Remove the bare-numeric default registrations `Monoid<int>`,
  `Monoid<long>`, `Monoid<std::size_t>`; migrate their uses
  (`monoid.test.cpp` asserts the additive int default today).
- The monad-induced monoids, named and unregistered for raw carriers:
  the Kleisli endomorphism monoid (identity = `pure`, combine =
  `kleisli`; the carrier is a function type, so it needs a named
  wrapper with erasure — precedent: `detail::LeftFoldProgram`), and the
  applicative-lifted monoid (`pure(identity_A)` /
  `invoke(combine_A, ·, ·)`). The Kleisli-form monad laws — `pure` is
  the unit of `>=>` — make the former the value-level statement of
  "a monad is a monoid in the endofunctors"; the categorical monoid
  itself is inexpressible at `Monoid<T>` (its tensor is composition,
  not product; the carrier is a constructor, not a type).

Acceptance: named carriers exist with monoid law tests; no
`Monoid<numeric>` primary registrations remain; `fold.hpp`'s boolean
monoids are the public ones.

## 2. Ground the full Functor instance in the Monad instance

Decision: conformance is structural — provide the operations, claim the
laws at the registration site. No adapter type and no nominal wrapper
requirement: the CRTP base is the adapter.

- `Monad<Impl>` grows the **basis** operation `fmap` (derived
  `bind(ma, pure ∘ f)`, preferring a native `Impl::fmap` when present,
  the same preference shape as `invoke`). Monad grows only basis
  operations of the classes it can ground, never their derived
  operations — `replace` comes from `Functor<>`, so monad-grounded
  instances track Functor's derived surface instead of drifting.
- The full instance is then spelled at registration:
  `Functor<OptionalMonadMap<T>>{}`. Compile-check the layered form —
  protected inheritance two deep plus the `static_cast<IMPL_BASE&>`
  access inside deducing-this members.
- Law test where a hand-written Functor coexists with a Monad
  (optional): `fmap f x == bind(x, pure ∘ f)` so the redundancy cannot
  drift.
- Two-concept discipline (revised 2026-09-07 from an earlier
  shallow-gate position): the concept for a typeclass *object* — what
  algorithms accept — checks **all** of the operations, derived ones
  included. Structural conformance permits hand-implementing an object
  without the CRTP base; a shallow gate (today's
  `applicative_object_for` probes `pure` only) passes such an object
  and defers the failure to whenever code written much later first
  reaches a derived operation, three frames deep. The deep concept
  moves that surprise to the gate, and doubles as the specification's
  statement of the class's full surface. The concept for an acceptable
  *Impl* is more restricted: the minimal complete bases only (with
  item 3, the alternate sets too) — the GHC parallel is class
  declaration vs `MINIMAL` pragma. Care: conditionally-available
  operations (`ap` only where the context can hold a callable,
  `subsume` only where the grade algebra licenses) are required
  conditionally, mirroring their wording constraints — a deep concept
  that demands `ap` unconditionally wrongly rejects the simd object.
  Derived operations templated over arbitrary callables are probed
  with representative instantiations — the check is a witness, not a
  proof, which suffices for the failure mode at issue (an operation
  missing entirely).
- Algorithms keep the explicit-object form as the primary spelling (as
  `traverse` does) so non-default instances can be forwarded in;
  lookup forms are sugar over it. Forced derivations forward
  structurally; choice-laden constructions (which monoid) fail the
  concept and must be constructed explicitly — the type system aligned
  with canonicity.

Acceptance: `Functor<SomeMonadMap>` compiles and passes functor laws;
agreement test in `laws.test.cpp`; invariant recorded.

## 3. Monad: admit the other complete bases (contingency)

Monad is deferred in D3200R0, so `monad.hpp` is less fleshed out than
`apply.hpp`: it admits exactly one basis, `pure` + `bind`. The
mechanism for alternate complete bases already exists twice —
Applicative's dual basis (`invoke` | `ap`) and Foldable's alternate
core (`fold_map` | `fold_right`) — and Monad should eventually accept
its other complete bases the same way:

- `pure` + `bind` (Kleisli triple — today's basis);
- `pure` + `fmap` + `join` (the monoidal presentation — unit and μ;
  `bind(ma, f) = join(fmap(f, ma))`);
- `pure` + `kleisli` is also complete, if awkward as a spelling.

Only the base's `bind` member needs the alternate path — every other
derived operation already routes through `self.bind`. Follow the
`apply.hpp` cycle discipline: each derivation addresses `Impl`
directly, so bind-from-join/fmap and join-from-bind cannot recurse into
each other. The `static_assert` diagnostic should name the minimal
sets, GHC-`MINIMAL`-style. Note for the paper: GHC cannot admit `join`
as a class method for roles/GND reasons; nothing constrains C++ the
same way, so the library can be more permissive than Haskell here.
This item also subsumes half of item 2: with the monoidal basis,
`fmap` is native rather than derived — one member, same preference
structure, and the general statement is that `Monad<Impl>` derives the
closure of whichever complete basis `Impl` supplies.

Required test case: a sender-shaped (lazy) monad, where the
alternate-basis derivations are exactly where the strictness
assumptions bite. The synthesized `invoke` already documents its
synchronous-`bind` assumption; `bind = join ∘ fmap` has the dual
assumption that `fmap` delivers a formed `M<M<A>>` for `join` to
flatten. For a lazy context the nested value is really a
`Lazy<M<A>>` — a thunk whose forcing (`get()`/start) yields `M<A>`.
Strictness handles the *semantics*: join-by-forcing (run outer, then
inner) is correct, and the demo `sender<T>`'s type erasure through
`std::function<T()>` makes `sender<sender<A>>` a real nameable type,
so it can carry the test. The hazard is the *type system inferring
things* on the unforced type: value_type-driven traits and the
derivations' deductions cannot distinguish `M<M<A>>` (nesting, join
it) from `M<B>` where `B = M<A>` (a payload that happens to be a
sender — do not join it). Acceptance tests: with a sender Monad
instance under each basis, `fmap(f, m)` for `f : A -> sender<B>`
yields `sender<sender<B>>` un-flattened while `bind(m, f)` yields
`sender<B>`, and the two bases agree on both. A real P2300 sender is
explicitly out of scope for these traits: there is no single `M` at
all — each adaptor is its own expression-template type, so recognizing
"the same context, nested" is a normalization problem for the item-4
era, not a trait fix here.

Motivating prose for the paper that picks this up: the nesting the
tests defend is the oldest bug in data modeling. SQL's NULL is a
`Maybe (Maybe a)` flattened to `Maybe a` at the model level — "no
spouse" (outer layer disengaged) and "spouse whose insurance is
unknown" (outer engaged, inner disengaged) collapse into one marker
that cannot carry the distinction; inner joins are bind-shaped, outer
joins introduce the outer Maybe, and both are necessary because they
answer different questions. Codd's later A-marks/I-marks split
(RM/T, RM V2) concedes that one bottom value serving every layer
destroyed information the model needed; three-valued logic and
`NULL != NULL` are the downstream wreckage. JavaScript's Promise
re-made the mistake — `then` auto-flattens, `Promise<Promise<T>>` is
unrepresentable, Promise is not a monad. `std::optional` already gets
it right (`transform` nests, `and_then` flattens, the caller picks).
The design position the acceptance tests encode: nesting is
meaningful, `join` is always an explicit caller-chosen operation, and
no derivation may flatten on the caller's behalf — the
`M<M<A>>`-vs-`M<B>`-where-`B = M<A>` inference ambiguity above is the
*reason* implicit flattening is forbidden, not a corner case to paper
over. An audience that has never wanted a monad has been burned by
SQL NULL; motivate fmap/bind from injury, not category theory.

Not scheduled: nothing proposed calls `bind`. Recorded so that if LEWG
says "do Monad now," the multi-basis surface is designed, not
improvised.

## 4. Functor combinators as evidence; higher kinds via Reflection (far horizon)

Definitely not part of this proposal. The library's deliberate dodge of
higher-kinded types — instances registered per specialization, result
contexts deduced from the function, never rebound from a constructor —
covers everything D3200R0 proposes. HKT pressure appears at exactly
three points: stating the categorical monoid (item 1's coda — the
carrier is a constructor, not a type), instance *families* defined once
per constructor rather than per specialization, and rebinding
`M<A> -> M<B>` with no function argument to deduce from. Two routes,
complementary rather than alternatives:

- **A small Types library, mostly buildable today.** The `base`-style
  functor combinators: `Identity<A>` and `Const<M, A>` (phantom `A`)
  are ordinary templates needing no HKT at all. `Const` snaps into
  item 1: its Applicative *requires* a Monoid on `M` (`pure` =
  `identity()`, application = `combine`), so `traverse` at the `Const`
  applicative **is** `fold_map` and `traverse` at `Identity` **is**
  `fmap` — precisely the foldMapDefault-style evidence the DELIBERATE
  CONSTRAINT comment in `traverse.hpp` promises, with the named
  monoids (`Const<Sum<int>, A>`) making the instances sayable.
  `Sum f g` (Functor, no Applicative — no `pure`) models the
  structural-conformance story at the combinator level: what is
  derivable is visible in which operations exist. Only `Compose` truly
  wants higher kinds; template-template parameters carry a workable
  version today, with the known warts (alias templates, hidden
  allocator parameters breaking unary-ness).
- **Reflection for the real thing.** `^^M` reifies the constructor as
  a `std::meta::info` value; `substitute(^^M, {^^A})` is application;
  `info` as an NTTP gives constructor-indexed lookup points
  (`hk_monad_typeclass<^^std::optional>`) beside the value-indexed
  ones, undisturbed. That buys the index, the rebind, and
  write-once family instances — not new runtime semantics: operations
  remain value-level code on real specializations. `substitute`'s
  kind-agnostic argument list is exactly where it beats
  template-template parameters (aliases, mixed kinds). Forward-compat
  answer for LEWG's "what about HKT?": the lookup pattern extends;
  sketch, not machinery.

Acceptance when picked up: `Identity`/`Const` instances plus the two
traverse-recovery theorems as tests; the rest stays prose until a paper
needs it.
