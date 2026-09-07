// include/beman/transpose/traverse.hpp                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_TRAVERSE_HPP
#define BEMAN_TRANSPOSE_TRAVERSE_HPP

#include <beman/transpose/apply.hpp>
#include <beman/transpose/detail/typeclass_base.hpp>
#include <beman/transpose/functor.hpp>

#include <concepts>
#include <type_traits>
#include <utility>

namespace beman::transpose {

/// Traversable pattern invariants:
/// - Instances are single lookup objects that provide traverse(F, T).
/// - transpose is a derived object operation implemented from
///   traverse(identity).
/// - Dispatch happens through a provided object or
///   traversable_typeclass<Concrete>.
/// - Traversal must preserve container shape while transposing structure and
///   context.

/// CRTP base for Traversable instances.
/// `Impl` must provide `traverse(applicative, f, container)` and declare
/// `element_type`. All other operations (`transpose`, `for_each`,
/// `traverse_with`, `transpose_with`) are derived.
///
/// DELIBERATE CONSTRAINT: Traversable does not and must not require a
/// Foldable instance (no Haskell-style superclass). `traverse` needs only
/// an Applicative and the walk; the fold family is proposed by the
/// companion recursive-tree-algorithms paper, and requiring it here would
/// put that paper's concept beneath this one after review. foldMapDefault-
/// style derivations (folding via traverse) remain possible as evidence,
/// never a requirement.
template <class Impl>
struct Traversable : protected Impl {
    static_assert(!std::is_same_v<Impl, std::false_type>,
                  "No traversable_typeclass<T> specialization found. "
                  "Specialize beman::transpose::traversable_typeclass<T> for "
                  "your type T, "
                  "provide traverse(applicative, F, T), and declare 'using "
                  "element_type = T;'.");
    static_assert(
        requires { typename Impl::element_type; },
        "Traversable Impl must declare 'using element_type = T;' "
        "so that transpose() and traverse_with() can deduce the element type.");
    // Alternate-core: Impl::traverse is the primitive; transpose is derived
    // from it. A transpose-primitive Impl would shadow transpose instead.
    using Impl::traverse;
    using element_type = typename Impl::element_type;

    // \ref{transpose.traversable.ops}, traversal operations
    template <class T, class F>
    auto for_each(this auto &&self, T &&value, F &&function);

    template <class T>
    auto transpose(this auto &&self, T &&value);

    // \ref{transpose.traversable.delegate}, delegated traversal
    template <class TRAVERSABLE_MAP, class T, class F>
    auto traverse_with(this auto &&, const TRAVERSABLE_MAP &traversable_map,
                       F &&function, T &&value);

    template <class TRAVERSABLE_MAP, class APPLICATIVE_MAP, class T, class F>
    auto traverse_with(this auto &&, const TRAVERSABLE_MAP &traversable_map,
                       const APPLICATIVE_MAP &applicative_map, F &&function,
                       T &&value);

    template <class TRAVERSABLE_MAP, class T>
    auto transpose_with(this auto &&self,
                        const TRAVERSABLE_MAP &traversable_map, T &&value);
};

//! \remarks This variable template is the lookup point for the Traversable
//! object of a structure type. A program may specialize it for a
//! program-defined structure. The primary template names no traversable
//! object.
template <class T>
inline constexpr auto traversable_typeclass = std::false_type{};

/// The applicative context `traverse(function, value)` would infer: the
/// return type of `function` applied to one element of `value`'s traversable
/// structure. Factored out so both the POLICY default and its constraint can
/// name it without repeating the computation. Exposition-only: it is named by
/// `traverse`'s declaration and by nothing else.
//! \expos
template <class F, class T>
using traverse_context_t = remove_cvref_t<std::invoke_result_t<
    F,
    const typename remove_cvref_t<
        decltype(traversable_typeclass<remove_cvref_t<T>>)>::element_type &>>;

//! \remarks This concept is satisfied when `POLICY` names an applicative
//! object over `CONTEXT`: it provides `pure`, returning exactly `CONTEXT`,
//! from `CONTEXT`'s element type. It is the minimal signature every
//! applicative object has, and constraining the trailing `traverse` policy
//! on it is what makes an argument that is not an applicative object -- a
//! further container, say -- ill-formed rather than silently accepted.
template <class POLICY, class CONTEXT>
concept applicative_object_for = requires(const POLICY &policy) {
    {
        policy.pure(std::declval<applicative_value_t<CONTEXT>>())
    } -> std::same_as<CONTEXT>;
};

// \rSec3[transpose.traversable.ops]{Traversal operations}

//! \effects Applies `function` to each element of `value` and transposes the
//! resulting contextual values, preserving the shape of `value`. The
//! applicative object is the one `applicative_typeclass` names for the
//! context `function` returns.
//! \returns The shape of `value` held in that single context.
//! \complexity Exactly one application of `function` per element of `value`.
//! \remarks Elements are visited in the structure's iteration order.
template <class Impl>
template <class T, class F>
auto Traversable<Impl>::for_each(this auto &&self, T &&value, F &&function) {
    using Context =
        remove_cvref_t<std::invoke_result_t<F, const element_type &>>;
    const auto &applicative = applicative_typeclass<Context>;
    return self.traverse(applicative, std::forward<F>(function),
                         std::forward<T>(value));
}

//! \constraints `element_type` is a context for which
//! `applicative_typeclass` names an applicative object.
//! \effects Equivalent to traversing `value` with the identity function: a
//! structure of contextual values becomes a single contextual value of the
//! structure, preserving shape.
//! \returns That single contextual value.
//! \remarks Elements are visited in the structure's iteration order.
template <class Impl>
template <class T>
auto Traversable<Impl>::transpose(this auto &&self, T &&value) {
    using Context = element_type;
    const auto &applicative = applicative_typeclass<Context>;
    return self.traverse(
        applicative, [](auto &&x) { return std::forward<decltype(x)>(x); },
        std::forward<T>(value));
}

// \rSec3[transpose.traversable.delegate]{Delegated traversal}

//! \effects Traverses `value` using the traversable object
//! `traversable_map` rather than `*this`. The applicative object is the one
//! `applicative_typeclass` names for the context `function` returns.
//! \returns The result of that traversal.
template <class Impl>
template <class TRAVERSABLE_MAP, class T, class F>
auto Traversable<Impl>::traverse_with(this auto &&,
                                      const TRAVERSABLE_MAP &traversable_map,
                                      F &&function, T &&value) {
    using Context = remove_cvref_t<std::invoke_result_t<
        F, const typename remove_cvref_t<TRAVERSABLE_MAP>::element_type &>>;
    const auto &applicative = applicative_typeclass<Context>;
    return traversable_map.traverse(applicative, std::forward<F>(function),
                                    std::forward<T>(value));
}

//! \effects-equiv
template <class Impl>
template <class TRAVERSABLE_MAP, class APPLICATIVE_MAP, class T, class F>
auto Traversable<Impl>::traverse_with(this auto &&,
                                      const TRAVERSABLE_MAP &traversable_map,
                                      const APPLICATIVE_MAP &applicative_map,
                                      F &&function, T &&value) {
    return traversable_map.traverse(applicative_map, std::forward<F>(function),
                                    std::forward<T>(value));
}

//! \effects-equiv
template <class Impl>
template <class TRAVERSABLE_MAP, class T>
auto Traversable<Impl>::transpose_with(this auto &&self,
                                       const TRAVERSABLE_MAP &traversable_map,
                                       T &&value) {
    return self.traverse_with(
        traversable_map, [](auto &&x) { return std::forward<decltype(x)>(x); },
        std::forward<T>(value));
}

// \rSec3[transpose.alg.traverse]{traverse}

//! \constraints `POLICY` satisfies `applicative_object_for` for the context
//! that applying `function` to an element of `value` yields.
//! \effects Applies `function` to each element of `value` and composes the
//! resulting contextual values with `policy`, preserving the shape of
//! `value`. Elements are visited in the structure's iteration order, and the
//! contextual values are composed in that same order.
//! \returns The shape of `value` held in the single context `policy`
//! composes into.
//! \complexity Exactly one application of `function` per element of `value`.
//! \remarks Let CONTEXT be the type that applying `function` to an element
//! of `value` yields. `POLICY` defaults to the type of the applicative
//! object `applicative_typeclass<CONTEXT>` names, which stops at the first
//! failing element, and the constraint is
//! `applicative_object_for<POLICY, CONTEXT>`. Passing the object
//! `accumulating_applicative_typeclass<CONTEXT>` names instead composes
//! every element's evidence. No element's context depends on another
//! element's value, so this is independent contextual composition rather
//! than sequential dependence.
template <class F, class T,
          class POLICY = remove_cvref_t<
              decltype(applicative_typeclass<traverse_context_t<F, T>>)>>
    requires applicative_object_for<POLICY, traverse_context_t<F, T>>
auto traverse(F &&function, T &&value, POLICY policy = POLICY{}) {
    const auto &map = traversable_typeclass<remove_cvref_t<T>>;
    return map.traverse(policy, std::forward<F>(function),
                        std::forward<T>(value));
}

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_TRAVERSE_HPP
