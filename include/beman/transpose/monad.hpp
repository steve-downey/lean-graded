// include/beman/transpose/monad.hpp                                  -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_MONAD_HPP
#define BEMAN_TRANSPOSE_MONAD_HPP

#include <beman/transpose/apply.hpp>
#include <beman/transpose/detail/typeclass_base.hpp>
#include <beman/transpose/grade.hpp>

#include <concepts>
#include <functional>
#include <optional>
#include <type_traits>
#include <utility>

namespace beman::transpose {

// EVIDENCE, NOT PROPOSED WORDING. D3200R0 does not propose a Monad
// abstraction — deferred, not rejected. Everything about the typeclass
// design leads to a consistent generic name for sequential composition
// eventually (today's and_then/transform/let_value are per-type members,
// not generic), and this header is the proof the mechanism carries Monad
// without strain. It is unproposed only because nothing in the coordinated
// set currently needs bind; the slot stays open for the paper that does.
// See D3200R0 "Why not Monad".

/** CRTP base for Monad instances.
 * `Impl` must provide `pure(value)` and `bind(ma, f)`.
 * The n-ary `invoke` is synthesized; `join` and `kleisli` are derived.
 * Monad does not inherit from Applicative, but provides the equivalent
 * applicative operation once `invoke` is synthesized from `bind` + `pure`.
 */
template <class Impl>
struct Monad : protected Impl {
    static_assert(!std::is_same_v<Impl, std::false_type>,
                  "No monad_typeclass<T> specialization found. "
                  "Specialize beman::transpose::monad_typeclass<T> for your "
                  "type T and provide pure(...) and bind(...) operations.");

    using Impl::bind;
    using Impl::pure;

    // invoke: n-ary lift synthesized from bind + pure (left-nested binds):
    //   invoke(f, m1, ..., mn) = m1 >>= \a1 -> ... mn >>= \an ->
    //   pure(f(a1...an))
    // Prefers a native Impl::invoke when present, like Applicative. This
    // derivation assumes a synchronous bind (the continuation is invoked
    // before bind returns), which holds for every Monad instance in this
    // repository.
    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&self, FUNCTION &&function, FIRST &&first,
                REST &&...rest) {
        if constexpr (requires {
                          impl_of(self).invoke(std::forward<FUNCTION>(function),
                                               std::forward<FIRST>(first),
                                               std::forward<REST>(rest)...);
                      }) {
            return impl_of(self).invoke(std::forward<FUNCTION>(function),
                                        std::forward<FIRST>(first),
                                        std::forward<REST>(rest)...);
        } else {
            return self.bind(std::forward<FIRST>(first), [&](auto &&head) {
                if constexpr (sizeof...(REST) == 0) {
                    return self.pure(std::invoke(
                        function, std::forward<decltype(head)>(head)));
                } else {
                    return self.invoke(
                        [&function, &head](auto &&...tail) {
                            return std::invoke(
                                function, head,
                                std::forward<decltype(tail)>(tail)...);
                        },
                        std::forward<REST>(rest)...);
                }
            });
        }
    }

    // join: flatten nested monad.
    // join mma = mma >>= id
    template <class MMA>
    auto join(this auto &&self, MMA &&mma) {
        return self.bind(std::forward<MMA>(mma),
                         [](auto &&inner) { return inner; });
    }

    // kleisli: forward Kleisli composition (>=>).
    // (f >=> g) a = f a >>= g
    template <class F, class G>
    auto kleisli(this auto &&self, F f, G g) {
        return [&self, f = std::move(f), g = std::move(g)](auto &&a) {
            return self.bind(f(std::forward<decltype(a)>(a)), g);
        };
    }

    /** ap: one-step contextual application, derived from bind + pure.
     *
     *   ap(mf, ma) = mf >>= \f -> ma >>= \a -> pure(f a)
     *
     * The Applicative base derives ap from its n-ary invoke; a monad-derived
     * instance has no invoke to derive from until one is synthesized, so it
     * gets ap from the bind basis instead. Both derivations exist exactly
     * when the context can hold a callable, and the constraint says so, so
     * the member disappears for contexts that cannot (std::simd::vec) rather
     * than failing inside the body.
     */
    template <class MF, class MA>
    auto ap(this auto &&self, MF &&mf, MA &&ma)
        requires requires {
            typename applicative_value_t<MF>;
            typename applicative_value_t<MA>;
            requires std::invocable<const applicative_value_t<MF> &,
                                    const applicative_value_t<MA> &>;
        }
    {
        return self.bind(std::forward<MF>(mf), [&self, &ma](auto &&function) {
            return self.bind(ma, [&self, &function](auto &&argument) {
                return self.pure(std::invoke(
                    function, std::forward<decltype(argument)>(argument)));
            });
        });
    }

    /** Uses a value at a wider grade, defaulted from the grade algebra.
     *
     * The same defaulted subsumption the Applicative base carries; see the
     * note there. Bind is the operation that joins grades, so the monad is
     * where widening is reached for most often.
     */
    template <class TARGET_GRADE, class CARRIER>
    constexpr auto subsume(this auto &&, CARRIER &&value)
        requires requires {
            grade_subsume<TARGET_GRADE>(std::forward<CARRIER>(value));
        }
    {
        return grade_subsume<TARGET_GRADE>(std::forward<CARRIER>(value));
    }

    // bind_with: explicit monad object override.
    template <class MONAD_MAP, class MA, class F>
    auto bind_with(this auto &&, const MONAD_MAP &monad_map, MA &&ma, F &&f) {
        return monad_map.bind(std::forward<MA>(ma), std::forward<F>(f));
    }

  private:
    //! \omit
    template <class SELF>
    static constexpr decltype(auto) impl_of(SELF &&self) {
        return static_cast<impl_ref_t<Impl, SELF>>(self);
    }
};

/** Typeclass lookup variable for Monad; specialize for each type. */
template <class T>
inline constexpr auto monad_typeclass = std::false_type{};

// -- std::optional monad instance --
// Delegates pure to the existing applicative_typeclass.

template <class VALUE_TYPE>
struct OptionalMonadImpl {
    using element_type = VALUE_TYPE;

    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<remove_cvref_t<VALUE>> {
        return applicative_typeclass<std::optional<VALUE_TYPE>>.pure(
            std::forward<VALUE>(value));
    }

    template <class A, class F>
    auto bind(this auto &&, const std::optional<A> &ma, F &&f) {
        using Result = remove_cvref_t<std::invoke_result_t<F, const A &>>;
        if (!ma)
            return Result{};
        return Result{std::invoke(std::forward<F>(f), *ma)};
    }
};

template <class VALUE_TYPE>
struct OptionalMonadMap : Monad<OptionalMonadImpl<VALUE_TYPE>> {
    using OptionalMonadImpl<VALUE_TYPE>::bind;
    using OptionalMonadImpl<VALUE_TYPE>::pure;
};

/** Monad instance for `std::optional<VALUE_TYPE>`. */
template <class VALUE_TYPE>
inline constexpr auto monad_typeclass<std::optional<VALUE_TYPE>> =
    OptionalMonadMap<VALUE_TYPE>{};

// -- Free-function API --

/** Sequences a monadic value `ma` through function `f` (Haskell's `>>=`). */
template <class MA, class F>
auto mbind(MA &&ma, F &&f) {
    const auto &map = monad_typeclass<remove_cvref_t<MA>>;
    return map.bind(std::forward<MA>(ma), std::forward<F>(f));
}

/** Flattens a nested monadic value; equivalent to `bind(mma, id)`. */
template <class MMA>
auto join(MMA &&mma) {
    const auto &map = monad_typeclass<remove_cvref_t<MMA>>;
    return map.join(std::forward<MMA>(mma));
}

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_MONAD_HPP
