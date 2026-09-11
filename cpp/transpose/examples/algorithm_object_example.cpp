// examples/algorithm_object_example.cpp                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Demonstrates the algorithm-object pattern: inheriting from typeclass
// instances to bring operations into unqualified scope.
// Shows single-typeclass (validate) and multi-typeclass (transform_if_large)
// composition, wrapped in niebloid CPOs.

#include "binary_tree.hpp"

#include <beman/transpose/fold.hpp>
#include <beman/transpose/traverse.hpp>

#include <cstddef>
#include <iostream>
#include <optional>
#include <utility>

namespace bt = beman::transpose;
using example::BinaryTree;

namespace example::algorithm {

namespace detail {

// validate_impl: inherits the Traversable typeclass for T.
// The typeclass operations (traverse, for_each) are available as unqualified
// member calls through `this->`.
template <class T, const auto &TC = beman::transpose::traversable_typeclass<
                       beman::transpose::remove_cvref_t<T>>>
struct validate_impl : beman::transpose::remove_cvref_t<decltype(TC)> {
    template <class Pred>
    auto call(Pred &&pred, const T &value) const {
        using element_type = typename beman::transpose::remove_cvref_t<
            decltype(TC)>::element_type;
        return this->for_each(
            value,
            [&](const element_type &elem) -> std::optional<element_type> {
                if (pred(elem))
                    return {elem};
                return std::nullopt;
            });
    }
};

// transform_if_large_impl: inherits both Foldable and Traversable for T.
// Demonstrates multi-typeclass composition — Foldable gives length,
// Traversable gives for_each. Both base classes are empty.
template <class T,
          const auto &FC = beman::transpose::foldable_typeclass<
              beman::transpose::remove_cvref_t<T>>,
          const auto &TC = beman::transpose::traversable_typeclass<
              beman::transpose::remove_cvref_t<T>>>
struct transform_if_large_impl
    : beman::transpose::remove_cvref_t<decltype(FC)>,
      beman::transpose::remove_cvref_t<decltype(TC)> {
    using foldable_base = beman::transpose::remove_cvref_t<decltype(FC)>;
    using traversable_base = beman::transpose::remove_cvref_t<decltype(TC)>;
    using element_type = typename traversable_base::element_type;

    template <class F>
    auto call(std::size_t min_size, F &&f, const T &value) const {
        auto n = this->foldable_base::length(value);
        if (n < min_size)
            return std::optional<T>{};

        return this->traversable_base::for_each(
            value,
            [&](const element_type &elem) -> std::optional<element_type> {
                return {f(elem)};
            });
    }
};

} // namespace detail

// validate: returns optional<Tree>; nullopt if any element fails the predicate.
struct validate_fn {
    template <class Pred, class T>
    auto operator()(Pred &&pred, T &&value) const {
        return detail::validate_impl<beman::transpose::remove_cvref_t<T>>{}
            .call(std::forward<Pred>(pred), std::forward<T>(value));
    }
};
inline constexpr validate_fn validate{};

// transform_if_large: applies f to every element only if the tree has at least
// min_size elements. Returns optional<Tree>: the transformed tree, or nullopt
// if too small. Shows Foldable + Traversable composition.
struct transform_if_large_fn {
    template <class F, class T>
    auto operator()(std::size_t min_size, F &&f, T &&value) const {
        return detail::transform_if_large_impl<
                   beman::transpose::remove_cvref_t<T>>{}
            .call(min_size, std::forward<F>(f), std::forward<T>(value));
    }
};
inline constexpr transform_if_large_fn transform_if_large{};

} // namespace example::algorithm

namespace algo = example::algorithm;

int main() {
    // tree: node(2) with left=leaf(3), right=leaf(5) — length=3, all positive
    auto tree = BinaryTree<int>::node(2, BinaryTree<int>::leaf(3),
                                      BinaryTree<int>::leaf(5));

    // --- validate: single-typeclass (Traversable) ---
    auto gt0 = [](int x) { return x > 0; };
    auto gt4 = [](int x) { return x > 4; };

    auto ok = algo::validate(gt0, tree);
    auto bad = algo::validate(gt4, tree);

    std::cout << "validate (all > 0): " << (ok ? "has value" : "empty") << '\n';
    std::cout << "validate (all > 4): " << (bad ? "has value" : "empty")
              << '\n';

    // --- transform_if_large: multi-typeclass (Foldable + Traversable) ---
    auto doubled = [](int x) { return x * 2; };

    auto big_enough = algo::transform_if_large(2, doubled, tree);
    auto too_small = algo::transform_if_large(10, doubled, tree);

    std::cout << "transform_if_large (min=2): "
              << (big_enough ? "has value" : "empty") << '\n';
    std::cout << "transform_if_large (min=10): "
              << (too_small ? "has value" : "empty") << '\n';

    return 0;
}
