// include/beman/transpose/simd.hpp                                   -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_SIMD_HPP
#define BEMAN_TRANSPOSE_SIMD_HPP

// Applicative instance for std::simd::basic_vec (P1928, C++26): the context
// that PROVES the invoke core. A vec<T> holds only vectorizable scalars, so
// vec<callable> is not a type: the classic `apply` (a callable held inside
// the context) could never be spelled here -- which is why this library has
// no apply anywhere, only the n-ary invoke. pure is the broadcast
// constructor; invoke is the lane-wise generator constructor.
//
// NOTE: this is an applicative instance only -- NOT a traversal context for
// rebuilding structures (a vec cannot hold a vector<T> either). It is the
// in-tree example of an Applicative that is not Traversable, the reason the
// two typeclasses are distinct. The traversal-capable lanewise context
// remains simd_lanes<T, N>.

#include <version>

// __has_include(<simd>) alone is not enough: libstdc++ ships the <simd>
// header unconditionally but leaves it empty unless the toolchain also
// supports expansion statements (P1306), so check its readiness macro too.
#if __has_include(<simd>) && __cplusplus > 202302L && defined(__glibcxx_simd)

#include <beman/transpose/apply.hpp>

#include <simd>

#include <functional>
#include <type_traits>
#include <utility>

namespace beman::transpose {

/** Applicative Impl for std::simd::basic_vec<T, ABI>: there is no vec of
 * callables to hold a function-in-context, so lane-wise application can
 * only be the n-ary invoke -- the concrete case that fixed this library's
 * single core. pure and invoke carry trailing return types / constraints so
 * every probe fails cleanly (SFINAE) rather than hard-erroring.
 */
template <class T, class ABI>
struct SimdVecApplicativeImpl {
    static constexpr auto width = std::simd::basic_vec<T, ABI>::size();

    /** Broadcast a scalar to every lane. */
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::simd::vec<remove_cvref_t<VALUE>, width>
        requires requires {
            std::simd::vec<remove_cvref_t<VALUE>, width>(
                std::forward<VALUE>(value));
        }
    {
        return std::simd::vec<remove_cvref_t<VALUE>, width>(
            std::forward<VALUE>(value));
    }

    /** N-ary core: a plain function applied lane by lane across the
     * operands, via the generator constructor. */
    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function, const FIRST &first,
                const REST &...rest)
        -> std::simd::vec<remove_cvref_t<std::invoke_result_t<
                              FUNCTION &, const typename FIRST::value_type &,
                              const typename REST::value_type &...>>,
                          width> {
        using U = remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const typename FIRST::value_type &,
                                 const typename REST::value_type &...>>;
        return std::simd::vec<U, width>([&](auto lane) -> U {
            return std::invoke(function, first[lane], rest[lane]...);
        });
    }
};

/** Invoke-only map: no native apply, and the base's derived apply cannot
 * instantiate for vec operands -- that non-instantiation is the point. */
template <class T, class ABI>
struct SimdVecApplicativeMap : Applicative<SimdVecApplicativeImpl<T, ABI>> {
    using SimdVecApplicativeImpl<T, ABI>::invoke;
    using SimdVecApplicativeImpl<T, ABI>::pure;
};

/** Registers the Applicative instance for std::simd::basic_vec<T, ABI>,
 * which the std::simd::vec<T, N> alias pattern-matches. */
template <class T, class ABI>
inline constexpr auto applicative_typeclass<std::simd::basic_vec<T, ABI>> =
    SimdVecApplicativeMap<T, ABI>{};

} // namespace beman::transpose

#endif // __has_include(<simd>) && __cplusplus > 202302L &&
       // defined(__glibcxx_simd)
#endif // BEMAN_TRANSPOSE_SIMD_HPP
