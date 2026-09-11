// tests/beman/transpose/sequence.test.cpp                            -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/sequence.hpp>

#include <catch2/catch_test_macros.hpp>

#include <optional>
#include <vector>

namespace bt = beman::transpose;

TEST_CASE("sequence: vector foldable length and to_vector") {
    const auto &f = bt::foldable_typeclass<std::vector<int>>;
    std::vector<int> xs{4, 5, 6};
    REQUIRE(f.length(xs) == 3);
    REQUIRE(f.to_vector(xs) == std::vector<int>{4, 5, 6});
    REQUIRE(f.fold_left(xs, 0, [](int a, int x) { return a + x; }) == 15);
}

TEST_CASE("sequence: vector foldable length takes the native path, no Map "
          "edit needed") {
    // VectorFoldableImpl grows a native length in this step; VectorFoldableMap
    // is untouched (no `using length;` was added). length must still answer
    // correctly for empty, one-element, and many-element vectors -- it is
    // now taking the native size()-based path instead of the fold_map-derived
    // one, and the answer must not move.
    const auto &f = bt::foldable_typeclass<std::vector<int>>;
    REQUIRE(f.length(std::vector<int>{}) == 0);
    REQUIRE(f.length(std::vector<int>{42}) == 1);
    REQUIRE(f.length(std::vector<int>{1, 2, 3, 4, 5}) == 5);
}

TEST_CASE("sequence: vector traversable primitive sequences effects") {
    const auto &t = bt::traversable_typeclass<std::vector<int>>;
    const auto &app = bt::applicative_typeclass<std::optional<int>>;
    auto result = t.traverse(
        app, [](int x) { return std::optional<int>{x + 1}; },
        std::vector<int>{1, 2, 3});
    REQUIRE(result == std::optional<std::vector<int>>{{2, 3, 4}});
}
