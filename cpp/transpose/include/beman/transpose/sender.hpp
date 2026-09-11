// include/beman/transpose/sender.hpp                                 -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_SENDER_HPP
#define BEMAN_TRANSPOSE_SENDER_HPP

// Non-normative demonstration type. sender models a deferred/asynchronous
// computational context for Paper A's second motivating domain. It is a
// deliberately minimal stand-in for a std::execution sender (P2300): a lazy
// value whose computation runs only when get() is called. Traversing a
// structure of senders transposes into a single sender of the structure, e.g.
// vector<sender<T>> becomes sender<vector<T>>, with no work performed until the
// resulting sender is run. It is illustrative, not a proposed standard type.

#include <beman/transpose/apply.hpp>

#include <functional>
#include <type_traits>
#include <utility>

namespace beman::transpose {

/** A minimal deferred (lazy) value: the wrapped computation runs on get().
 * @tparam T the eventual result type
 */
template <class T>
struct sender {
    using value_type = T;

    std::function<T()> run;

    /** Runs the deferred computation and returns its result. */
    auto get() const -> T { return run(); }

    /** Build a sender that is already ready with @p value. */
    static auto ready(T value) -> sender {
        return sender{[value = std::move(value)]() -> T { return value; }};
    }

    /** Equality runs both deferred computations and compares the results. */
    friend auto operator==(const sender &left, const sender &right) -> bool
        requires requires(const T &a, const T &b) {
            { a == b } -> std::convertible_to<bool>;
        }
    {
        return left.get() == right.get();
    }
};

/** Invoke-native Applicative instance for sender<T> with deferred semantics.
 *
 * pure(x) yields a ready sender of x. invoke(f, s1, ..., sn) yields a single
 * new sender that, when run, runs every operand and applies the plain
 * function f to the results -- one deferred call capturing everything, so
 * laziness is preserved by construction. No work happens until the composed
 * sender is run.
 */
template <class T>
struct SenderApplicativeImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value) {
        using U = remove_cvref_t<VALUE>;
        return sender<U>::ready(U(std::forward<VALUE>(value)));
    }

    /** N-ary deferred core; SFINAE-friendly via the trailing return type. */
    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function, const sender<FIRST> &first,
                const sender<REST> &...rest)
        -> sender<remove_cvref_t<std::invoke_result_t<
            const remove_cvref_t<FUNCTION> &, FIRST, REST...>>> {
        using U = remove_cvref_t<std::invoke_result_t<
            const remove_cvref_t<FUNCTION> &, FIRST, REST...>>;
        return sender<U>{[function = remove_cvref_t<FUNCTION>(
                              std::forward<FUNCTION>(function)),
                          first, rest...]() -> U {
            return std::invoke(function, first.get(), rest.get()...);
        }};
    }
};

/** Applicative map exposing pure and the n-ary invoke core for sender<T>. */
template <class T>
struct SenderApplicativeMap : Applicative<SenderApplicativeImpl<T>> {
    using SenderApplicativeImpl<T>::invoke;
    using SenderApplicativeImpl<T>::pure;
};

/** Registers SenderApplicativeMap as the Applicative instance for sender<T>. */
template <class T>
inline constexpr auto applicative_typeclass<sender<T>> =
    SenderApplicativeMap<T>{};

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_SENDER_HPP
