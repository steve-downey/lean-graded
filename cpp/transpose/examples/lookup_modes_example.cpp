// examples/lookup_modes_example.cpp                                   -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Demonstrates the three lookup modes that distinguish the typeclass-object
// pattern from plain specialization: implicit lookup, explicit object
// argument, and NTTP pinning.

#include <beman/transpose/functor.hpp>

#include <iostream>
#include <optional>

namespace bt = beman::transpose;

// NTTP pinning: the typeclass object is captured at template instantiation
// time.
template <class CONTEXT, const auto &FUNCTOR = bt::functor_typeclass<CONTEXT>>
auto fmap_plus_one(const CONTEXT &value) {
    return FUNCTOR.fmap([](int x) { return x + 1; }, value);
}

int main() {
    std::optional<int> value{41};

    // Mode 1: Implicit lookup — retrieve the typeclass object via the
    // functor_typeclass variable template and call fmap on it.
    const auto &functor = bt::functor_typeclass<std::optional<int>>;
    auto result1 = functor.fmap([](int x) { return x + 1; }, value);
    std::cout << "implicit lookup:  " << result1.value_or(-1) << "\n";

    // Mode 2: Explicit object argument — pass the typeclass object explicitly
    // to a function that uses it by const ref.
    auto fmap_with = [](const auto &tc, const auto &val) {
        return tc.fmap([](int x) { return x + 1; }, val);
    };
    auto result2 = fmap_with(bt::functor_typeclass<std::optional<int>>, value);
    std::cout << "explicit object:  " << result2.value_or(-1) << "\n";

    // Mode 3: NTTP pinning — the typeclass object is fixed at the
    // instantiation site, not at the call site.
    std::optional<int> small{9};
    auto result3 = fmap_plus_one(small);
    std::cout << "NTTP pinning:     " << result3.value_or(-1) << "\n";

    return 0;
}
