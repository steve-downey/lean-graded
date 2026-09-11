// examples/fold_example.cpp                                          -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// `fold` derives many reductions (length, fold_left, any_of, ...) from a
// single fold_map primitive on the looked-up Foldable instance.

#include <beman/transpose/fold.hpp>
#include <beman/transpose/sequence.hpp>

#include <iostream>
#include <vector>

namespace bt = beman::transpose;

int main() {
    const auto &f = bt::foldable_typeclass<std::vector<int>>;
    std::vector<int> xs{1, 2, 3, 4, 5};

    std::cout << "length: " << f.length(xs) << '\n';
    std::cout << "sum: "
              << f.fold_left(xs, 0, [](int a, int x) { return a + x; }) << '\n';
    std::cout << "any > 4: "
              << (f.any_of(xs, [](int x) { return x > 4; }) ? "yes" : "no")
              << '\n';

    return 0;
}
