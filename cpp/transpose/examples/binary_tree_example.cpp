// examples/binary_tree_example.cpp                                    -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Demonstrates the typeclass-object pattern on a recursive data type:
// BinaryTree<T> with Foldable (length, fold_left), Applicative (invoke),
// and Traversable (traverse with optional).

#include "binary_tree.hpp"

#include <beman/transpose/apply.hpp>
#include <beman/transpose/fold.hpp>
#include <beman/transpose/traverse.hpp>

#include <iostream>
#include <optional>

namespace bt = beman::transpose;
using example::BinaryTree;

int main() {
    // tree: node(2) with left=leaf(3), right=leaf(5)
    // in-order: 3, 2, 5 — length=3, sum=10
    auto tree = BinaryTree<int>::node(2, BinaryTree<int>::leaf(3),
                                      BinaryTree<int>::leaf(5));

    // --- Foldable ---
    const auto &f = bt::foldable_typeclass<BinaryTree<int>>;
    std::cout << "Foldable:\n";
    std::cout << "  length: " << f.length(tree) << '\n';
    std::cout << "  sum:    " << f.fold_left(tree, 0, [](int a, int x) {
        return a + x;
    }) << '\n';

    // --- Applicative ---
    const auto &app = bt::applicative_typeclass<BinaryTree<int>>;
    auto doubled = app.invoke([](int x) { return x * 2; }, tree);
    std::cout << "Applicative:\n";
    std::cout << "  doubled sum: " << f.fold_left(doubled, 0, [](int a, int x) {
        return a + x;
    }) << '\n';

    // --- Traversable ---
    auto non_negative = [](int x) -> std::optional<int> {
        return x >= 0 ? std::optional<int>{x} : std::optional<int>{};
    };

    auto neg_tree = BinaryTree<int>::node(-1, BinaryTree<int>::leaf(2),
                                          BinaryTree<int>::leaf(3));

    auto all_positive = bt::traverse(non_negative, tree);
    auto has_negative = bt::traverse(non_negative, neg_tree);

    std::cout << "Traversable:\n";
    std::cout << "  all positive: " << (all_positive ? "has value" : "empty")
              << '\n';
    std::cout << "  has negative: " << (has_negative ? "has value" : "empty")
              << '\n';

    return 0;
}
