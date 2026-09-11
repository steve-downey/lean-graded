// tests/beman/transpose/test_support.hpp                             -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_TEST_TEST_SUPPORT_HPP
#define BEMAN_TRANSPOSE_TEST_TEST_SUPPORT_HPP

#include <beman/transpose/apply.hpp>
#include <beman/transpose/fold.hpp>
#include <beman/transpose/traverse.hpp>

#include <algorithm>
#include <functional>
#include <utility>
#include <vector>

namespace beman::transpose::test {

// Law helpers are spelled through the n-ary invoke core, the only
// application form in this library (the classic ap/apply spellings were
// removed 2026-07-14; see apply.hpp's pattern invariants). Availability
// probes are NAMED CONCEPTS on purpose: a bare requires-expression at block
// scope hard-errors on an invalid expression instead of yielding false
// ([expr.prim.req]).

/** True when the Map exposes one-step contextual application (`ap`, the
 * classic basis kept as a secondary operation) for these operands. It is
 * available exactly when the context can hold a callable; the probe pins
 * its absence where it cannot (std::simd::vec). */
template <class MAP, class FUNCTIONS_IN_CONTEXT, class ARGUMENTS_IN_CONTEXT>
concept has_apply_form =
    requires(const MAP &map, const FUNCTIONS_IN_CONTEXT &cf,
             const ARGUMENTS_IN_CONTEXT &cx) { map.apply(cf, cx); } ||
    requires(const MAP &map, const FUNCTIONS_IN_CONTEXT &cf,
             const ARGUMENTS_IN_CONTEXT &cx) { map.ap(cf, cx); };

/** Verify the Applicative identity law, invoke form: `map(id, v) == v`.
 * Holds for every context, including those that cannot hold callables. */
template <class CONTEXT>
auto check_applicative_identity_law(const CONTEXT &value) -> bool {
    const auto &applicative = applicative_typeclass<remove_cvref_t<CONTEXT>>;
    auto result = applicative.map([](const auto &x) { return x; }, value);
    return result == value;
}

/** Verify the Applicative homomorphism law, generalized to the n-ary core:
 * `invoke(f, pure(x1), ..., pure(xn)) == pure(f(x1, ..., xn))`. */
template <class CONTEXT, class FUNCTION, class... VALUES>
auto check_applicative_homomorphism_law(const FUNCTION &function,
                                        const VALUES &...values) -> bool {
    const auto &applicative = applicative_typeclass<remove_cvref_t<CONTEXT>>;
    auto left = applicative.invoke(function, applicative.pure(values)...);
    auto right = applicative.pure(std::invoke(function, values...));
    return left == right;
}

/** Verify the Applicative interchange law, invoke form:
 * `invoke(eval, u, pure(y)) == map(f -> f(y), u)` -- floating a pure
 * operand out of an application. Instantiable only for contexts whose
 * *elements* are callables (a plain vector-of-lambdas is fine); no apply
 * verb is involved. */
template <class FUNCTIONS_IN_CONTEXT, class VALUE>
auto check_applicative_interchange_law(const FUNCTIONS_IN_CONTEXT &functions,
                                       const VALUE &value) -> bool {
    const auto &applicative =
        applicative_typeclass<remove_cvref_t<FUNCTIONS_IN_CONTEXT>>;
    auto call = [](const auto &f, const auto &x) { return std::invoke(f, x); };
    auto left = applicative.invoke(call, functions, applicative.pure(value));
    auto right = applicative.map(
        [&value](const auto &f) { return std::invoke(f, value); }, functions);
    return left == right;
}

/** Verify the functor composition law: `map(f . g, v) == map(f, map(g, v))`
 * -- the composition analog expressible for every applicative context. */
template <class CONTEXT, class F, class G>
auto check_functor_composition_law(const F &outer, const G &inner,
                                   const CONTEXT &value) -> bool {
    const auto &applicative = applicative_typeclass<remove_cvref_t<CONTEXT>>;
    auto left = applicative.map(
        [&](const auto &x) {
            return std::invoke(outer, std::invoke(inner, x));
        },
        value);
    auto right = applicative.map(outer, applicative.map(inner, value));
    return left == right;
}

/** Minimal single-element applicative context used in law tests. */
template <class VALUE_TYPE>
struct Identity {
    using value_type = VALUE_TYPE;

    VALUE_TYPE value;

    friend auto operator==(const Identity &, const Identity &)
        -> bool = default;
};

/** Ordered multi-element foldable context backed by `std::vector`. */
template <class VALUE_TYPE>
struct Sequence {
    using value_type = VALUE_TYPE;

    std::vector<VALUE_TYPE> values;

    friend auto operator==(const Sequence &, const Sequence &)
        -> bool = default;
};

} // namespace beman::transpose::test

namespace beman::transpose {

/** Applicative implementation for Identity<V>: pure wraps, invoke unwraps
 * every operand and calls the plain function once. */
template <class VALUE_TYPE>
struct TestIdentityApplicativeImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value) {
        return test::Identity<remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function,
                const test::Identity<FIRST> &first,
                const test::Identity<REST> &...rest)
        -> test::Identity<remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>> {
        using Result = remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>;
        return test::Identity<Result>{
            std::invoke(function, first.value, rest.value...)};
    }
};

template <class VALUE_TYPE>
struct TestIdentityApplicativeMap
    : Applicative<TestIdentityApplicativeImpl<VALUE_TYPE>> {
    using TestIdentityApplicativeImpl<VALUE_TYPE>::invoke;
    using TestIdentityApplicativeImpl<VALUE_TYPE>::pure;
};

template <class VALUE_TYPE>
inline constexpr auto applicative_typeclass<test::Identity<VALUE_TYPE>> =
    TestIdentityApplicativeMap<VALUE_TYPE>{};

/** Foldable implementation for Sequence<V>: fold_map walks values
 * left-to-right. */
template <class VALUE_TYPE>
struct TestSequenceFoldableImpl {
    template <class FUNCTION>
    auto fold_map(this auto &&, FUNCTION &&function,
                  const test::Sequence<VALUE_TYPE> &sequence) {
        using Result =
            remove_cvref_t<std::invoke_result_t<FUNCTION, const VALUE_TYPE &>>;
        return std::ranges::fold_left(
            sequence.values, monoid_identity<Result>(),
            [&](Result acc, const VALUE_TYPE &value) {
                return monoid_combine(std::move(acc),
                                      std::invoke(function, value));
            });
    }
};

template <class VALUE_TYPE>
struct TestSequenceFoldableMap
    : Foldable<TestSequenceFoldableImpl<VALUE_TYPE>> {
    using TestSequenceFoldableImpl<VALUE_TYPE>::fold_map;
};

template <class VALUE_TYPE>
inline constexpr auto foldable_typeclass<test::Sequence<VALUE_TYPE>> =
    TestSequenceFoldableMap<VALUE_TYPE>{};

/** Traversable implementation for Identity<V>. */
template <class VALUE_TYPE>
struct TestIdentityTraversableImpl {
    using element_type = VALUE_TYPE;

    template <class APPLICATIVE, class FUNCTION>
    auto traverse(this auto &&, const APPLICATIVE &applicative,
                  FUNCTION &&function,
                  const test::Identity<VALUE_TYPE> &identity) {
        return applicative.invoke(
            [](auto &&value) {
                using U = remove_cvref_t<decltype(value)>;
                return test::Identity<U>{std::forward<decltype(value)>(value)};
            },
            std::invoke(std::forward<FUNCTION>(function), identity.value));
    }
};

template <class VALUE_TYPE>
struct TestIdentityTraversableMap
    : Traversable<TestIdentityTraversableImpl<VALUE_TYPE>> {
    using TestIdentityTraversableImpl<VALUE_TYPE>::traverse;
};

template <class VALUE_TYPE>
inline constexpr auto traversable_typeclass<test::Identity<VALUE_TYPE>> =
    TestIdentityTraversableMap<VALUE_TYPE>{};

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_TEST_TEST_SUPPORT_HPP
