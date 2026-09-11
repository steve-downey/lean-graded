// tests/beman/transpose/expected.test.cpp                            -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/expected.hpp>

#include <beman/transpose/sequence.hpp>
#include <beman/transpose/transpose.hpp>
#include <beman/transpose/traverse.hpp>

#include "test_support.hpp"

#include <catch2/catch_test_macros.hpp>

#include <beman/transpose/error_set.hpp>

#include <expected>
#include <ios>
#include <string>
#include <system_error>
#include <type_traits>
#include <vector>

namespace bt = beman::transpose;

namespace {

using errc = std::errc;
using exp_int = std::expected<int, errc>;

auto fail(errc code) -> exp_int { return exp_int{std::unexpect, code}; }

/** Only positive inputs succeed; the rest carry a distinguishable error. */
auto positive(int x) -> exp_int {
    if (x > 0) {
        return exp_int{x * 2};
    }
    return fail(errc::invalid_argument);
}

} // namespace

TEST_CASE("expected: applicative pure and invoke") {
    const auto &app = bt::applicative_typeclass<exp_int>;

    REQUIRE(app.pure(7) == std::expected<int, errc>{7});

    auto sum =
        app.invoke([](int a, int b) { return a + b; }, exp_int{2}, exp_int{3});
    REQUIRE(sum == exp_int{5});
}

TEST_CASE("expected: invoke short-circuits and the leftmost error wins") {
    const auto &app = bt::applicative_typeclass<exp_int>;
    auto add = [](int a, int b, int c) { return a + b + c; };

    // Effect order is observable and part of the contract: with two failing
    // operands, the LEFTMOST error is the one propagated.
    auto both_fail = app.invoke(add, exp_int{1}, fail(errc::invalid_argument),
                                fail(errc::result_out_of_range));
    REQUIRE_FALSE(both_fail.has_value());
    REQUIRE(both_fail.error() == errc::invalid_argument);

    auto later_fails = app.invoke(add, exp_int{1}, exp_int{2},
                                  fail(errc::result_out_of_range));
    REQUIRE_FALSE(later_fails.has_value());
    REQUIRE(later_fails.error() == errc::result_out_of_range);
}

TEST_CASE("expected: applicative map and the derived operations") {
    const auto &app = bt::applicative_typeclass<exp_int>;

    auto mapped = app.map([](int x) { return x * 1.5; }, exp_int{4});
    REQUIRE(mapped == std::expected<double, errc>{6.0});

    auto mapped_error =
        app.map([](int x) { return x * 1.5; }, fail(errc::invalid_argument));
    REQUIRE_FALSE(mapped_error.has_value());
    REQUIRE(mapped_error.error() == errc::invalid_argument);

    REQUIRE(app.discard_first(exp_int{1}, exp_int{2}) == exp_int{2});
    REQUIRE(app.discard_second(exp_int{1}, exp_int{2}) == exp_int{1});
}

TEST_CASE("expected: monad bind short-circuits") {
    const auto &monad = bt::monad_typeclass<exp_int>;

    auto to_text = [](int x) {
        return std::expected<std::string, errc>{std::to_string(x)};
    };

    REQUIRE(monad.bind(exp_int{12}, to_text) ==
            std::expected<std::string, errc>{"12"});

    auto short_circuited = monad.bind(fail(errc::invalid_argument), to_text);
    REQUIRE_FALSE(short_circuited.has_value());
    REQUIRE(short_circuited.error() == errc::invalid_argument);
}

TEST_CASE("expected: monad join flattens") {
    auto nested = std::expected<exp_int, errc>{exp_int{9}};
    REQUIRE(bt::join(nested) == exp_int{9});

    auto outer_failed =
        std::expected<exp_int, errc>{std::unexpect, errc::invalid_argument};
    REQUIRE(bt::join(outer_failed).error() == errc::invalid_argument);
}

TEST_CASE("expected: traverse over a vector transposes into one expected") {
    auto ok = bt::traverse(positive, std::vector<int>{1, 2, 3});
    REQUIRE(ok == std::expected<std::vector<int>, errc>{{2, 4, 6}});

    auto bad = bt::traverse(positive, std::vector<int>{1, -1, 3});
    REQUIRE_FALSE(bad.has_value());
    REQUIRE(bad.error() == errc::invalid_argument);
}

TEST_CASE("expected: traverse preserves shape and empty is pure") {
    auto empty = bt::traverse(positive, std::vector<int>{});
    REQUIRE(empty == std::expected<std::vector<int>, errc>{std::vector<int>{}});

    auto result = bt::traverse(positive, std::vector<int>{5, 4, 3, 2, 1});
    REQUIRE(result.has_value());
    REQUIRE(*result == std::vector<int>{10, 8, 6, 4, 2});
}

TEST_CASE("expected: transpose a vector of expected") {
    auto all_ok =
        bt::transpose(std::vector<exp_int>{exp_int{1}, exp_int{2}, exp_int{3}});
    REQUIRE(all_ok == std::expected<std::vector<int>, errc>{{1, 2, 3}});

    auto one_bad = bt::transpose(std::vector<exp_int>{
        exp_int{1}, fail(errc::result_out_of_range), exp_int{3}});
    REQUIRE_FALSE(one_bad.has_value());
    REQUIRE(one_bad.error() == errc::result_out_of_range);
}

TEST_CASE("expected: mixing two error types joins them into an error_set") {
    using mixed = bt::error_set<errc, std::io_errc>;
    const auto &app = bt::applicative_typeclass<exp_int>;

    auto add = [](int a, int b) { return a + b; };
    std::expected<int, std::io_errc> io_ok{10};

    auto both_ok = app.invoke(add, exp_int{5}, io_ok);
    static_assert(std::is_same_v<decltype(both_ok), std::expected<int, mixed>>);
    REQUIRE(both_ok == std::expected<int, mixed>{15});

    // Each side's error widens into the joined set, keeping its identity.
    auto left_failed = app.invoke(add, fail(errc::invalid_argument), io_ok);
    REQUIRE_FALSE(left_failed.has_value());
    REQUIRE(left_failed.error().holds<errc>());

    std::expected<int, std::io_errc> io_bad{std::unexpect,
                                            std::io_errc::stream};
    auto right_failed = app.invoke(add, exp_int{5}, io_bad);
    REQUIRE_FALSE(right_failed.has_value());
    REQUIRE(right_failed.error().holds<std::io_errc>());
}

TEST_CASE("expected: a bare operand is promoted and leaves no trace") {
    const auto &app = bt::applicative_typeclass<exp_int>;
    auto add = [](int a, int b) { return a + b; };

    // The bare 5 is empty-graded, so the join is a no-op and the result is
    // still expected<int, errc> -- NOT expected<int, error_set<errc>>.
    auto result = app.invoke(add, exp_int{37}, 5);
    static_assert(std::is_same_v<decltype(result), exp_int>);
    REQUIRE(result == exp_int{42});

    auto short_circuited = app.invoke(add, fail(errc::invalid_argument), 5);
    REQUIRE_FALSE(short_circuited.has_value());
    REQUIRE(short_circuited.error() == errc::invalid_argument);
}

TEST_CASE("expected: graded bind joins the continuation's error") {
    using mixed = bt::error_set<errc, std::io_errc>;
    const auto &monad = bt::monad_typeclass<exp_int>;

    auto to_io = [](int x) {
        return std::expected<double, std::io_errc>{static_cast<double>(x)};
    };

    auto ok = monad.bind(exp_int{4}, to_io);
    static_assert(std::is_same_v<decltype(ok), std::expected<double, mixed>>);
    REQUIRE(ok == std::expected<double, mixed>{4.0});

    // The upstream error widens rather than being lost.
    auto upstream = monad.bind(fail(errc::invalid_argument), to_io);
    REQUIRE_FALSE(upstream.has_value());
    REQUIRE(upstream.error().holds<errc>());

    auto downstream = monad.bind(exp_int{4}, [](int) {
        return std::expected<double, std::io_errc>{std::unexpect,
                                                   std::io_errc::stream};
    });
    REQUIRE_FALSE(downstream.has_value());
    REQUIRE(downstream.error().holds<std::io_errc>());
}

TEST_CASE("expected: an existing error_set absorbs rather than nests") {
    using set_errc = bt::error_set<errc>;
    using mixed = bt::error_set<errc, std::io_errc>;

    const auto &app = bt::applicative_typeclass<std::expected<int, set_errc>>;
    auto add = [](int a, int b) { return a + b; };

    std::expected<int, set_errc> already_a_set{3};
    std::expected<int, std::io_errc> io_ok{4};

    auto joined = app.invoke(add, already_a_set, io_ok);
    static_assert(std::is_same_v<decltype(joined), std::expected<int, mixed>>);
    REQUIRE(joined == std::expected<int, mixed>{7});
}

TEST_CASE("expected: for_each over the Identity traversable") {
    const auto &t = bt::traversable_typeclass<bt::test::Identity<int>>;
    auto result = t.for_each(bt::test::Identity<int>{20}, positive);
    REQUIRE(result == std::expected<bt::test::Identity<int>, errc>{
                          bt::test::Identity<int>{40}});
}
