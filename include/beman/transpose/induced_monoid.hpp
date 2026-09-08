// include/beman/transpose/induced_monoid.hpp                        -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_INDUCED_MONOID_HPP
#define BEMAN_TRANSPOSE_INDUCED_MONOID_HPP

#include <beman/transpose/apply.hpp>
#include <beman/transpose/monad.hpp>
#include <beman/transpose/monoid.hpp>

#include <functional>
#include <utility>

// EVIDENCE, NOT PROPOSED WORDING. These are two monoids the library's own
// typeclass instances induce, not a facility D3200R0 proposes: a Monad
// induces a monoid on its Kleisli arrows, and an Applicative induces a
// monoid on its context lifted from a monoid on the element. Both are named
// carriers with their own `Monoid` specialization, and neither is
// registered for any raw carrier -- see
// docs/decisions.md#monoid-carrier-canonicity. This header exists to show
// the mechanism carries the induction without strain, and to record, once,
// the one thing worth not rediscovering: the categorical statement "a monad
// is a monoid in the category of endofunctors" is inexpressible at
// `Monoid<T>`, whose tensor is a product and whose carrier is a type, not a
// type constructor. The Kleisli endomorphism monoid below is the value-level
// statement that survives that gap -- evidence of the theorem, not the
// theorem itself.

namespace beman::transpose {

/** A Kleisli arrow `A -> M<A>`, type-erased through `std::function` so that
 * `combine` can return the same type it takes -- the same erasure
 * `detail::LeftFoldProgram` (`fold.hpp`) uses for the same reason: a
 * monoid's carrier must close under `combine`, and a bare lambda type does
 * not.
 *
 * `MONAD_OBJECT` is a type parameter, not a value: every typeclass object in
 * this library is stateless and empty, so `Monoid<KleisliEndo<...>>` -- which
 * has no member in which to keep an instance -- default-constructs a fresh
 * `MONAD_OBJECT{}` wherever it needs one. That construction is free, not a
 * workaround.
 */
template <class MONAD_OBJECT, class A>
struct KleisliEndo {
    /** What `MONAD_OBJECT::pure` returns when applied to an `A`; the context
     * every arrow in this monoid returns into.
     */
    using result_type = decltype(std::declval<const MONAD_OBJECT &>().pure(
        std::declval<const A &>()));

    std::function<result_type(const A &)> d_run;

    auto operator()(const A &a) const -> result_type { return d_run(a); }
};

/** Monoid<KleisliEndo<MONAD_OBJECT, A>>: identity is `pure`, combine is
 * Kleisli composition (`>=>`). The Kleisli-form monad laws -- `pure` is the
 * two-sided unit of `>=>`, and `>=>` is associative -- are exactly this
 * monoid's laws, which is the whole reason to name the carrier: it is the
 * value-level statement of "a monad is a monoid in the category of
 * endofunctors", the only form of that statement this library can make.
 *
 * `combine` builds its own `MONAD_OBJECT{}` inside the stored lambda, at the
 * moment the lambda is called, rather than storing the result of
 * `MONAD_OBJECT{}.kleisli(...)` directly. `Monad<Impl>::kleisli`'s derived
 * branch returns a closure that captures `self` by reference; storing that
 * closure here would capture a reference to a `MONAD_OBJECT{}` temporary
 * that no longer exists once `combine` has returned. Constructing the
 * temporary and invoking `kleisli` on it in the same full expression that
 * calls the result keeps the temporary alive for exactly as long as it is
 * used.
 */
template <class MONAD_OBJECT, class A>
struct Monoid<KleisliEndo<MONAD_OBJECT, A>> {
    using Endo = KleisliEndo<MONAD_OBJECT, A>;
    using result_type = typename Endo::result_type;

    auto identity() const -> Endo {
        return Endo{
            [](const A &a) -> result_type { return MONAD_OBJECT{}.pure(a); }};
    }

    auto combine(const Endo &lhs, const Endo &rhs) const -> Endo {
        return Endo{[lhs, rhs](const A &a) -> result_type {
            return MONAD_OBJECT{}.kleisli(lhs, rhs)(a);
        }};
    }
};

/** `CONTEXT` (e.g. `std::optional<A>`) as a monoid, lifted from a `Monoid<A>`
 * through an `APPLICATIVE_OBJECT` over `CONTEXT`: identity is
 * `pure(identity_A)`, combine is `invoke(combine_A, ·, ·)`.
 *
 * `APPLICATIVE_OBJECT` is a type parameter for the same reason
 * `MONAD_OBJECT` is above: every typeclass object is stateless and empty, so
 * default-constructing a fresh one wherever `Monoid<LiftedMonoid<...>>` needs
 * one costs nothing.
 */
template <class APPLICATIVE_OBJECT, class CONTEXT>
struct LiftedMonoid {
    CONTEXT d_value;

    friend constexpr auto operator==(const LiftedMonoid &,
                                     const LiftedMonoid &) -> bool = default;
};

/** Monoid<LiftedMonoid<APPLICATIVE_OBJECT, CONTEXT>>: identity lifts `A`'s
 * identity with `pure`; combine lifts `A`'s combine with `invoke`.
 *
 * Uses `invoke`, not `ap`: `invoke` is the interface that works for every
 * context, including one that cannot hold a callable (`apply.hpp`'s
 * "Applicative pattern invariants" block), whereas `ap` requires the context
 * to be able to hold the (curried) combining function.
 */
template <class APPLICATIVE_OBJECT, class CONTEXT>
struct Monoid<LiftedMonoid<APPLICATIVE_OBJECT, CONTEXT>> {
    using A = applicative_value_t<CONTEXT>;
    using Lifted = LiftedMonoid<APPLICATIVE_OBJECT, CONTEXT>;

    auto identity() const -> Lifted {
        return Lifted{APPLICATIVE_OBJECT{}.pure(monoid_v<A>.identity())};
    }

    auto combine(const Lifted &lhs, const Lifted &rhs) const -> Lifted {
        return Lifted{APPLICATIVE_OBJECT{}.invoke(
            [](const A &a, const A &b) { return monoid_v<A>.combine(a, b); },
            lhs.d_value, rhs.d_value)};
    }
};

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_INDUCED_MONOID_HPP
