// include/beman/transpose/simd_lanes.hpp                              -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_SIMD_LANES_HPP
#define BEMAN_TRANSPOSE_SIMD_LANES_HPP

// Non-normative demonstration type. simd_lanes models a fixed-width lanewise
// applicative context for Paper A's SIMD domain, backed by std::simd::vec for
// arithmetic element types. Unlike zip_list (which has dynamic/infinite width),
// simd_lanes has a compile-time width N matching a hardware SIMD register.
//
// Transposing a structure of simd_lanes produces a simd_lanes of structures:
//   vector<simd_lanes<T, N>>  ->  simd_lanes<vector<T>, N>
//
// The general storage is std::array<T, N> because the transposed result may
// hold non-arithmetic T (e.g., vector<int>). Examples show construction from
// std::simd::vec for the arithmetic case.

#include <beman/transpose/apply.hpp>

#include <array>
#include <cstddef>
#include <functional>
#include <type_traits>
#include <utility>

namespace beman::transpose {

template <class T, int N>
struct simd_lanes {
    using value_type = T;
    static constexpr int width = N;

    std::array<T, N> data;

    static auto repeat(T value) -> simd_lanes {
        simd_lanes result;
        result.data.fill(value);
        return result;
    }

    friend auto operator==(const simd_lanes &, const simd_lanes &)
        -> bool = default;
};

template <class T, int N>
struct SimdLanesApplicativeImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value) {
        using U = remove_cvref_t<VALUE>;
        return simd_lanes<U, N>::repeat(U(std::forward<VALUE>(value)));
    }

    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function, const FIRST &first,
                const REST &...rest) {
        using Result =
            std::invoke_result_t<FUNCTION, const typename FIRST::value_type &,
                                 const typename REST::value_type &...>;
        using U = remove_cvref_t<Result>;

        simd_lanes<U, N> result;
        for (int i = 0; i < N; ++i) {
            result.data[i] =
                std::invoke(function, first.data[i], rest.data[i]...);
        }
        return result;
    }
};

/** Applicative map for simd_lanes<T, N>: the native n-ary invoke core. */
template <class T, int N>
struct SimdLanesApplicativeMap : Applicative<SimdLanesApplicativeImpl<T, N>> {
    using SimdLanesApplicativeImpl<T, N>::invoke;
    using SimdLanesApplicativeImpl<T, N>::pure;
};

template <class T, int N>
inline constexpr auto applicative_typeclass<simd_lanes<T, N>> =
    SimdLanesApplicativeMap<T, N>{};

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_SIMD_LANES_HPP
