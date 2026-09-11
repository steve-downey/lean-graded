// examples/traverse_example.cpp                                      -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// `traverse` applies an effectful function to each element of a structure and
// transposes the results, preserving shape on success.

#include <beman/transpose/sequence.hpp>
#include <beman/transpose/traverse.hpp>

#include <iostream>
#include <optional>
#include <vector>

namespace bt = beman::transpose;

// Parse-like validation: succeed only for non-negative inputs.
static auto checked_double(int x) -> std::optional<int> {
    return x >= 0 ? std::optional<int>{x * 2} : std::optional<int>{};
}

int main() {
    auto good = bt::traverse(checked_double, std::vector<int>{1, 2, 3});
    std::cout << "all valid: " << (good ? "yes" : "no") << '\n';

    auto bad = bt::traverse(checked_double, std::vector<int>{1, -2, 3});
    std::cout << "one invalid: " << (bad ? "yes" : "no") << '\n';

    return 0;
}
