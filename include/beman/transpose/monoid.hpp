// include/beman/transpose/monoid.hpp                                 -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_MONOID_HPP
#define BEMAN_TRANSPOSE_MONOID_HPP

#include <beman/transpose/detail/typeclass_base.hpp>

#include <cstddef>
#include <limits>
#include <string>
#include <utility>
#include <vector>

namespace beman::transpose {

// Monoid pattern invariants:
// - Monoid<T> is the customization point; specialize identity/combine together.
// - monoid_v<T> is the canonical lookup object used by generic algorithms.
// - identity and combine must stay coherent for a single associative law
//   domain.
// - Prefer adding new Monoid<T> specializations over ad hoc free functions.

/** Customization point for the Monoid typeclass.
 * Specialize this struct for type `VALUE_TYPE` and provide
 * `identity()` and `combine(lhs, rhs)` to make that type usable
 * wherever a Monoid is required (e.g., as the result type of fold_map).
 */
template <class VALUE_TYPE>
struct Monoid;

/** Canonical lookup object for Monoid<VALUE_TYPE>; used by generic algorithms.
 */
template <class VALUE_TYPE>
inline constexpr Monoid<VALUE_TYPE> monoid_v = Monoid<VALUE_TYPE>{};

/** Opaque count accumulator; the Monoid combines by addition. */
struct Count {
    std::size_t d_value;

    friend constexpr bool operator==(const Count &lhs,
                                     const Count &rhs) = default;
};

/** Monoid<Count>: identity is zero, combine adds counts. */
template <>
struct Monoid<Count> {
    constexpr auto identity() const -> Count { return Count{0}; }

    constexpr auto combine(const Count &lhs, const Count &rhs) const -> Count {
        return Count{lhs.d_value + rhs.d_value};
    }
};

/// Numbers and booleans carry more than one monoid -- addition, product,
/// max, min, any, all -- so no bare `Monoid<int>`, `Monoid<long>`, or
/// `Monoid<std::size_t>` is registered here.
/// A raw numeric registration would make the library choose one of those on
/// the caller's behalf; the choice is spelled instead by a named carrier
/// (`Sum<int>`, `Product<int>`, `Max<int>`, `Any`, ...).
/// See docs/decisions.md#monoid-carrier-canonicity.

/** Additive monoid carrier: combine adds, identity is the zero of `T`. */
template <class T>
struct Sum {
    T d_value;

    friend constexpr bool operator==(const Sum &, const Sum &) = default;
};

/** Monoid<Sum<T>>: identity is `T{}`, combine adds. */
template <class T>
struct Monoid<Sum<T>> {
    constexpr auto identity() const -> Sum<T> { return Sum<T>{T{}}; }

    constexpr auto combine(const Sum<T> &lhs, const Sum<T> &rhs) const
        -> Sum<T> {
        return Sum<T>{lhs.d_value + rhs.d_value};
    }
};

/** Multiplicative monoid carrier: combine multiplies, identity is `T{1}`. */
template <class T>
struct Product {
    T d_value;

    friend constexpr bool operator==(const Product &,
                                     const Product &) = default;
};

/** Monoid<Product<T>>: identity is `T{1}`, combine multiplies. */
template <class T>
struct Monoid<Product<T>> {
    constexpr auto identity() const -> Product<T> { return Product<T>{T{1}}; }

    constexpr auto combine(const Product<T> &lhs, const Product<T> &rhs) const
        -> Product<T> {
        return Product<T>{lhs.d_value * rhs.d_value};
    }
};

/** Maximum monoid carrier: combine takes the larger of the two.
 * The identity is the saturating lower bound of `T` -- negative infinity
 * where `T` has one, `std::numeric_limits<T>::lowest()` otherwise -- not an
 * adjoined identity element and not a `std::optional`. A `Max<T>` on a type
 * whose `numeric_limits` is not specialized has no identity and therefore no
 * `Monoid`; that is the correct outcome, not a gap.
 */
template <class T>
struct Max {
    T d_value;

    friend constexpr bool operator==(const Max &, const Max &) = default;
};

/** Monoid<Max<T>>: identity is the saturating lower bound of `T`, combine
 * takes the larger of the two.
 */
template <class T>
struct Monoid<Max<T>> {
    constexpr auto identity() const -> Max<T> {
        if constexpr (std::numeric_limits<T>::has_infinity) {
            return Max<T>{-std::numeric_limits<T>::infinity()};
        } else {
            return Max<T>{std::numeric_limits<T>::lowest()};
        }
    }

    constexpr auto combine(const Max<T> &lhs, const Max<T> &rhs) const
        -> Max<T> {
        return Max<T>{lhs.d_value > rhs.d_value ? lhs.d_value : rhs.d_value};
    }
};

/** Minimum monoid carrier: combine takes the smaller of the two.
 * The identity is the saturating upper bound of `T` -- positive infinity
 * where `T` has one, `std::numeric_limits<T>::max()` otherwise -- not an
 * adjoined identity element and not a `std::optional`. A `Min<T>` on a type
 * whose `numeric_limits` is not specialized has no identity and therefore no
 * `Monoid`; that is the correct outcome, not a gap.
 */
template <class T>
struct Min {
    T d_value;

    friend constexpr bool operator==(const Min &, const Min &) = default;
};

/** Monoid<Min<T>>: identity is the saturating upper bound of `T`, combine
 * takes the smaller of the two.
 */
template <class T>
struct Monoid<Min<T>> {
    constexpr auto identity() const -> Min<T> {
        if constexpr (std::numeric_limits<T>::has_infinity) {
            return Min<T>{std::numeric_limits<T>::infinity()};
        } else {
            return Min<T>{std::numeric_limits<T>::max()};
        }
    }

    constexpr auto combine(const Min<T> &lhs, const Min<T> &rhs) const
        -> Min<T> {
        return Min<T>{lhs.d_value < rhs.d_value ? lhs.d_value : rhs.d_value};
    }
};

/** Disjunctive monoid carrier: combine is logical or, identity is `false`. */
struct Any {
    bool d_value;

    friend constexpr bool operator==(const Any &, const Any &) = default;
};

/** Monoid<Any>: identity is `false`, combine is logical or. */
template <>
struct Monoid<Any> {
    constexpr auto identity() const -> Any { return Any{false}; }

    constexpr auto combine(Any lhs, Any rhs) const -> Any {
        return Any{lhs.d_value || rhs.d_value};
    }
};

/** Conjunctive monoid carrier: combine is logical and, identity is `true`. */
struct All {
    bool d_value;

    friend constexpr bool operator==(const All &, const All &) = default;
};

/** Monoid<All>: identity is `true`, combine is logical and. */
template <>
struct Monoid<All> {
    constexpr auto identity() const -> All { return All{true}; }

    constexpr auto combine(All lhs, All rhs) const -> All {
        return All{lhs.d_value && rhs.d_value};
    }
};

/** Monoid<std::string>: concatenation monoid with identity "". */
template <>
struct Monoid<std::string> {
    auto identity() const -> std::string { return {}; }

    auto combine(const std::string &lhs, const std::string &rhs) const
        -> std::string {
        return lhs + rhs;
    }
};

/** Monoid<std::vector<T>>: concatenation monoid with identity empty vector. */
template <class VALUE_TYPE>
struct Monoid<std::vector<VALUE_TYPE>> {
    auto identity() const -> std::vector<VALUE_TYPE> { return {}; }

    auto combine(std::vector<VALUE_TYPE> lhs,
                 const std::vector<VALUE_TYPE> &rhs) const
        -> std::vector<VALUE_TYPE> {
        lhs.insert(lhs.end(), rhs.begin(), rhs.end());
        return lhs;
    }
};

/** Returns the identity element for the Monoid of VALUE_TYPE. */
template <class VALUE_TYPE>
auto monoid_identity() -> VALUE_TYPE {
    return monoid_v<VALUE_TYPE>.identity();
}

/** Combines two values using the Monoid of VALUE_TYPE. */
template <class VALUE_TYPE>
auto monoid_combine(const VALUE_TYPE &lhs, const VALUE_TYPE &rhs)
    -> VALUE_TYPE {
    return monoid_v<VALUE_TYPE>.combine(lhs, rhs);
}

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_MONOID_HPP
