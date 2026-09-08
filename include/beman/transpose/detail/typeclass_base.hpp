// include/beman/transpose/detail/typeclass_base.hpp                  -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_DETAIL_TYPECLASS_BASE_HPP
#define BEMAN_TRANSPOSE_DETAIL_TYPECLASS_BASE_HPP

#include <optional>
#include <type_traits>

namespace beman::transpose {

// Design invariants for the typeclass object pattern:
// - Per-concept lookup objects (for example *_typeclass<T>) are the
//   customization lookup points for typeclass dispatch.
// - Generic algorithms call through looked-up typeclass objects.
// - New concepts should keep lookup static and explicit.
// - Avoid adding parallel ADL-only customization paths for the same concept.

template <class T>
using remove_cvref_t = std::remove_cvref_t<T>;

/** Always false, but dependent on a template parameter pack.
 *
 * A `static_assert` written directly with `false` fires as soon as the
 * enclosing template is parsed, even if the member it guards is never
 * called. Making the condition depend on the pack defers the check to
 * instantiation, so it fires only when someone actually calls the guarded
 * operation -- which is what lets a member give a custom "this operation
 * does not exist, here is why" diagnostic instead of a bare "no member"
 * error.
 */
template <class...>
inline constexpr bool always_false_v = false;

/** The `Impl` sub-object reference a typeclass base's member should address,
 * given the deduced type of its `self` parameter.
 *
 * Every derived operation on a typeclass base takes the same shape: probe
 * `Impl` for a native version of the operation, forward to it if it is
 * there, derive otherwise. Both halves address `Impl` rather than `self`,
 * which is what keeps two mutually-derivable operations from recursing into
 * each other. This spells the const propagation that addressing needs, once.
 *
 * The cast itself cannot live here. Each base inherits its `Impl`
 * protectedly, so only a member of that base may perform the conversion;
 * each base carries a three-line private `impl_of` that does, and they all
 * name this alias. See `docs/decisions.md#impl-access-through-bases`.
 */
template <class IMPL, class SELF>
using impl_ref_t =
    std::conditional_t<std::is_const_v<std::remove_reference_t<SELF>>,
                       const IMPL, IMPL> &;

/** Trait that extracts the element type from an applicative container.
 * Primary template uses the nested `value_type` alias when present.
 */
template <class T, class = void>
struct applicative_value;

template <class T>
struct applicative_value<T,
                         std::void_t<typename remove_cvref_t<T>::value_type>> {
    using type = typename remove_cvref_t<T>::value_type;
};

template <class T>
struct applicative_value<std::optional<T>, void> {
    using type = T;
};

/** Convenience alias for `applicative_value<T>::type`. */
template <class T>
using applicative_value_t = typename applicative_value<remove_cvref_t<T>>::type;

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_DETAIL_TYPECLASS_BASE_HPP
