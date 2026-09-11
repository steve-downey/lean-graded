// examples/apply_example.cpp                                         -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// `invoke` lifts a plain function and applies it to several effectful
// arguments, short-circuiting when any argument is absent.

#include <beman/transpose/apply.hpp>

#include <iostream>
#include <optional>

namespace bt = beman::transpose;

int main() {
    const auto &app = bt::applicative_typeclass<std::optional<int>>;
    auto sum3 = [](int a, int b, int c) { return a + b + c; };

    auto ok = app.invoke(sum3, std::optional<int>{1}, std::optional<int>{2},
                         std::optional<int>{3});
    std::cout << "sum present: " << (ok ? *ok : -1) << '\n';

    auto missing = app.invoke(sum3, std::optional<int>{1}, std::optional<int>{},
                              std::optional<int>{3});
    std::cout << "sum missing: " << (missing ? "has value" : "empty") << '\n';

    return 0;
}
