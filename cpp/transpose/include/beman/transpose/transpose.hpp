// include/beman/transpose/transpose.hpp                              -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_TRANSPOSE_HPP
#define BEMAN_TRANSPOSE_TRANSPOSE_HPP

// Umbrella header for beman.transpose plus the front-door `transpose` verb.
//
// `transpose` flips a structure of contextual values into a single contextual
// value of the structure, preserving shape:
//
//   structure<context<T>>  ->  context<structure<T>>
//
// It is `traverse` with the identity function; the context's applicative is
// inferred from the structure's element type.

#include <beman/transpose/config.hpp>

#include <beman/transpose/apply.hpp>
#include <beman/transpose/array.hpp>
#include <beman/transpose/dual_monoid.hpp>
#include <beman/transpose/error_set.hpp>
#include <beman/transpose/expected.hpp>
#include <beman/transpose/fold.hpp>
#include <beman/transpose/functor.hpp>
#include <beman/transpose/grade.hpp>
#include <beman/transpose/monad.hpp>
#include <beman/transpose/monoid.hpp>
#include <beman/transpose/sender.hpp>
#include <beman/transpose/sequence.hpp>
#include <beman/transpose/traverse.hpp>
#include <beman/transpose/zip_list.hpp>

#if __has_include(<simd>)
#include <beman/transpose/simd.hpp> // self-gates further on C++26
#include <beman/transpose/simd_lanes.hpp>
#endif

#include <utility>

namespace beman::transpose {

// \rSec3[transpose.alg.transpose]{transpose}

//! \constraints `traversable_typeclass` names a traversable object for
//! `value`'s type, and `applicative_typeclass` names an applicative object
//! for that structure's element type.
//! \effects Equivalent to traversing `value` with the identity function: a
//! structure of contextual values, `structure<context<T>>`, becomes a single
//! contextual value of the structure, `context<structure<T>>`, preserving
//! shape. The applicative object is inferred from the structure's element
//! type.
//! \returns That single contextual value.
//! \complexity Linear in the number of elements of `value`.
//! \remarks Elements are visited in the structure's iteration order, and
//! their contexts are composed in that same order.
template <class T>
auto transpose(T &&value) {
    const auto &map = traversable_typeclass<remove_cvref_t<T>>;
    return map.transpose(std::forward<T>(value));
}

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_TRANSPOSE_HPP
