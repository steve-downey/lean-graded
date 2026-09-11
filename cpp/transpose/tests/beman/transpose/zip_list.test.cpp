// tests/beman/transpose/zip_list.test.cpp                            -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/zip_list.hpp>

#include "test_support.hpp"

#include <catch2/catch_test_macros.hpp>

#include <vector>

namespace bt = beman::transpose;

TEST_CASE("zip_list: pure repeats infinitely") {
    auto r = bt::applicative_typeclass<bt::zip_list<int>>.pure(7);
    REQUIRE(r.is_repeating());
    REQUIRE(r.repeated == 7);
}

TEST_CASE("zip_list: apply zips positionally and truncates to shortest") {
    const auto &app = bt::applicative_typeclass<bt::zip_list<int>>;
    auto result =
        app.invoke([](int a, int b) { return a + b; },
                   bt::zip_list<int>{{1, 2, 3}}, bt::zip_list<int>{{10, 20}});
    REQUIRE(result.data == std::vector<int>{11, 22});
}

TEST_CASE("zip_list: pure operand acts as identity for truncation") {
    const auto &app = bt::applicative_typeclass<bt::zip_list<int>>;
    auto result =
        app.invoke([](int a, int b) { return a * b; },
                   bt::zip_list<int>{{1, 2, 3}}, bt::zip_list<int>::repeat(10));
    REQUIRE(result.data == std::vector<int>{10, 20, 30});
}

TEST_CASE("zip_list: applicative laws hold") {
    using bt::test::check_applicative_homomorphism_law;
    using bt::test::check_applicative_identity_law;
    using bt::test::check_applicative_interchange_law;
    using bt::test::check_functor_composition_law;

    REQUIRE(check_applicative_identity_law(bt::zip_list<int>{{1, 2, 3}}));
    REQUIRE(check_applicative_homomorphism_law<bt::zip_list<int>>(
        [](int a, int b) { return a + b; }, 4, 5));

    auto double_it = [](int x) { return x * 2; };
    auto negate_it = [](int x) { return -x; };
    bt::zip_list<decltype(double_it)> functions;
    functions.data = {double_it, double_it};
    REQUIRE(check_applicative_interchange_law(functions, 21));
    REQUIRE(check_functor_composition_law(double_it, negate_it,
                                          bt::zip_list<int>{{3, 4, 5}}));
}

TEST_CASE("zip_list: derived ap agrees with the invoke basis") {
    // zip_list is invoke-basis; the secondary ap is derived as
    // invoke(eval, fs, xs) and must agree with the direct spelling.
    const auto &app = bt::applicative_typeclass<bt::zip_list<int>>;
    auto add_ten = [](int x) { return x + 10; };
    bt::zip_list<decltype(add_ten)> functions;
    functions.data = {add_ten, add_ten, add_ten};
    auto via_ap = app.ap(functions, bt::zip_list<int>{{1, 2, 3, 4}});
    auto via_invoke = app.invoke([](const auto &f, int x) { return f(x); },
                                 functions, bt::zip_list<int>{{1, 2, 3, 4}});
    REQUIRE(via_ap.data == via_invoke.data);
    REQUIRE(via_ap.data == std::vector<int>{11, 12, 13});
}
