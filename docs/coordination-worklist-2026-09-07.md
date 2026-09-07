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
- Forwarding invariant to document beside the SFINAE-friendliness rule
  in `apply.hpp`: algorithm constraints stay shallow and structural
  (`applicative_object_for` probes `pure` only) **because** every
  object registered or passed is full by construction — a wrapped Map,
  never a bare Impl. Algorithms keep the explicit-object form as the
  primary spelling (as `traverse` does) so non-default instances can be
  forwarded in; lookup forms are sugar over it. Forced derivations
  forward structurally; choice-laden constructions (which monoid) fail
  the concept and must be constructed explicitly — the type system
  aligned with canonicity.

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

Not scheduled: nothing proposed calls `bind`. Recorded so that if LEWG
says "do Monad now," the multi-basis surface is designed, not
improvised.
