// installtest/test.cpp                                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/transpose.hpp>

#include <iostream>
#include <optional>
#include <vector>

int main() {
    namespace bt = beman::transpose;

    std::vector<std::optional<int>> in{{1}, {2}, {3}};
    auto out = bt::transpose(in);

    if (!out) {
        std::cerr << "expected all elements present\n";
        return 1;
    }

    std::cout << "transpose: |";
    for (int value : *out) {
        std::cout << value << ' ';
    }
    std::cout << "|\n";
    return 0;
}
