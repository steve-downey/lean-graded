// include/beman/transpose/traverse.hpp                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_TRAVERSE_HPP
#define BEMAN_TRANSPOSE_TRAVERSE_HPP

#include <beman/transpose/apply.hpp>
#include <beman/transpose/detail/typeclass_base.hpp>
#include <beman/transpose/functor.hpp>

#include <concepts>
#include <optional>
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

  private:
    //! \omit
    template <class SELF>
    static constexpr decltype(auto) impl_of(SELF &&self) {
        return static_cast<impl_ref_t<Impl, SELF>>(self);
    }
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

//! \remarks This concept is satisfied when `POLICY` is an `applicative_object`
//! over `CONTEXT` whose `pure` returns exactly `CONTEXT` from `CONTEXT`'s
//! element type. The exact-return-type requirement is stronger than
//! `applicative_object` itself makes -- that concept only asks that `pure`
//! exist -- and it is what `traverse`'s trailing policy parameter needs:
//! composing element results into anything other than `CONTEXT` itself would
//! not preserve `traverse`'s "shape of `value` held in context" contract.
//! Constraining the policy parameter on the full deep concept, not merely on
//! `pure`, is what makes an argument that is not a real applicative object --
//! a further container, say -- ill-formed rather than silently accepted.
template <class POLICY, class CONTEXT>
concept applicative_object_for =
    applicative_object<POLICY, CONTEXT> && requires(const POLICY &policy) {
        {
            policy.pure(std::declval<applicative_value_t<CONTEXT>>())
        } -> std::same_as<CONTEXT>;
    };

//! \remarks This concept is satisfied when `OBJ` provides the full
//! Traversable object surface over `STRUCTURE`: `traverse`, `for_each` and
//! `traverse_with`, each probed with a representative witness callable that
//! lifts an element into `std::optional` (always a registered applicative
//! context, for any element type). `transpose` and `transpose_with` are
//! required only where `OBJ::element_type` itself names a registered
//! applicative context: both are hard-wired to
//! `applicative_typeclass<element_type>`, which names no applicative object
//! for a structure like `std::vector<int>` whose elements are not
//! themselves an applicative context -- transposing such a structure is not
//! a meaningful operation, not a missing one, so this concept treats
//! `transpose`/`transpose_with` as conditional the same way
//! `applicative_object` treats `ap` and `subsume`. This concept does not
//! require a Foldable object: Traversable needs only an Applicative and the
//! walk, the DELIBERATE CONSTRAINT `Traversable` itself carries.
template <class OBJ, class STRUCTURE>
concept traversable_object =
    requires(const OBJ &obj, const STRUCTURE &structure) {
        obj.traverse(
            applicative_typeclass<std::optional<applicative_value_t<STRUCTURE>>>,
            probe_witness<std::optional<applicative_value_t<STRUCTURE>>>{},
            structure);
        obj.for_each(
            structure,
            probe_witness<std::optional<applicative_value_t<STRUCTURE>>>{});
        obj.traverse_with(
            obj, probe_witness<std::optional<applicative_value_t<STRUCTURE>>>{},
            structure);
    } &&
    (!requires(const OBJ &) {
        applicative_typeclass<typename OBJ::element_type>.pure(
            std::declval<typename OBJ::element_type>());
    } || requires(const OBJ &obj, const STRUCTURE &structure) {
        obj.transpose(structure);
        obj.transpose_with(obj, structure);
    });

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
