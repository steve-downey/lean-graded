// tests/beman/transpose/functor.test.cpp                             -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/functor.hpp>

#include <catch2/catch_test_macros.hpp>

#include <optional>
#include <vector>

namespace bt = beman::transpose;

TEST_CASE("functor: fmap over optional") {
    const auto &f = bt::functor_typeclass<std::optional<int>>;
    REQUIRE(f.fmap([](int x) { return x + 1; }, std::optional<int>{41}) ==
            std::optional<int>{42});
    REQUIRE(f.fmap([](int x) { return x + 1; }, std::optional<int>{}) ==
            std::optional<int>{});
}

TEST_CASE("functor: fmap over vector") {
    const auto &f = bt::functor_typeclass<std::vector<int>>;
    REQUIRE(f.fmap([](int x) { return x * 2; }, std::vector<int>{1, 2, 3}) ==
            std::vector<int>{2, 4, 6});
}

TEST_CASE("functor: replace is derived from fmap") {
    const auto &f = bt::functor_typeclass<std::vector<int>>;
    REQUIRE(f.replace(std::vector<int>{1, 2, 3}, 0) ==
            std::vector<int>{0, 0, 0});
}

namespace {
// A Functor Impl with a native `replace` that is observably not the
// derivation: it replaces with the replacement *twice over*, so a test can
// tell which member ran.
struct MarkedReplaceImpl {
    template <class F>
    auto fmap(this auto &&, F &&function, const std::vector<int> &values) {
        std::vector<int> output;
        output.reserve(values.size());
        for (const auto &v : values) {
            output.push_back(function(v));
        }
        return output;
    }

    template <class T, class U>
    auto replace(this auto &&, T &&value, U &&replacement) {
        return std::vector<int>(value.size(), replacement + replacement);
    }
};

struct MarkedReplaceMap : bt::Functor<MarkedReplaceImpl> {};
} // namespace

TEST_CASE("functor: replace prefers a native Impl::replace") {
    MarkedReplaceMap m{};
    REQUIRE(m.replace(std::vector<int>{1, 2, 3}, 5) ==
            std::vector<int>{10, 10, 10});
}
