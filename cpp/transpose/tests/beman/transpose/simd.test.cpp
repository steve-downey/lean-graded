// tests/beman/transpose/simd.test.cpp                                -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

// Tests for the std::simd::basic_vec applicative: the invoke-only context.
// Gated exactly like examples/simd_example.cpp -- real code only on a C++26
// toolchain with <simd>; otherwise a single SUCCEED so Catch2 discovery
// never sees an empty binary.

#include <version>

// __has_include(<simd>) alone is not enough: libstdc++ ships the <simd>
// header unconditionally but leaves it empty unless the toolchain also
// supports expansion statements (P1306), so check its readiness macro too.
#if __has_include(<simd>) && __cplusplus > 202302L && defined(__glibcxx_simd)

#include <beman/transpose/simd.hpp>

#include "test_support.hpp"

#include <catch2/catch_test_macros.hpp>

#include <simd>

namespace bt = beman::transpose;

using vec4 = std::simd::vec<int, 4>;

namespace {
auto lanes_equal(const vec4 &left, const vec4 &right) -> bool {
    for (int lane = 0; lane < 4; ++lane) {
        if (left[lane] != right[lane]) {
            return false;
        }
    }
    return true;
}
} // namespace

TEST_CASE("simd: pure broadcasts to every lane") {
    const auto &app = bt::applicative_typeclass<vec4>;
    auto r = app.pure(9);
    REQUIRE(lanes_equal(r, vec4(9)));
}

TEST_CASE("simd: invoke applies a plain function lane by lane") {
    const auto &app = bt::applicative_typeclass<vec4>;
    vec4 a([](int lane) { return lane + 1; });        // {1, 2, 3, 4}
    vec4 b([](int lane) { return (lane + 1) * 10; }); // {10, 20, 30, 40}
    vec4 c(2);                                        // {2, 2, 2, 2}

    auto unary = app.invoke([](int x) { return -x; }, a);
    REQUIRE(lanes_equal(unary, vec4([](int lane) { return -(lane + 1); })));

    auto binary = app.invoke([](int x, int y) { return x + y; }, a, b);
    REQUIRE(
        lanes_equal(binary, vec4([](int lane) { return (lane + 1) * 11; })));

    auto ternary =
        app.invoke([](int x, int y, int z) { return (x + y) * z; }, a, b, c);
    REQUIRE(
        lanes_equal(ternary, vec4([](int lane) { return (lane + 1) * 22; })));
}

TEST_CASE("simd: map and zip_with are derived from the invoke core") {
    const auto &app = bt::applicative_typeclass<vec4>;
    vec4 a([](int lane) { return lane; }); // {0, 1, 2, 3}

    auto mapped = app.map([](int x) { return x * x; }, a);
    REQUIRE(lanes_equal(mapped, vec4([](int lane) { return lane * lane; })));

    auto zipped = app.zip_with([](int x, int y) { return x * y; }, a, a);
    REQUIRE(lanes_equal(zipped, vec4([](int lane) { return lane * lane; })));
}

TEST_CASE("simd: applicative laws hold in invoke form") {
    const auto &app = bt::applicative_typeclass<vec4>;

    // Identity: map(id, v) == v.
    vec4 v([](int lane) { return 3 * lane + 1; });
    REQUIRE(lanes_equal(app.map([](int x) { return x; }, v), v));

    // Homomorphism, n-ary: invoke(f, pure(x)...) == pure(f(x...)).
    auto add = [](int x, int y) { return x + y; };
    REQUIRE(lanes_equal(app.invoke(add, app.pure(20), app.pure(22)),
                        app.pure(add(20, 22))));

    // Composition, functor form: map(f . g, v) == map(f, map(g, v)).
    auto outer = [](int x) { return x * 2; };
    auto inner = [](int x) { return x + 5; };
    REQUIRE(lanes_equal(app.map([&](int x) { return outer(inner(x)); }, v),
                        app.map(outer, app.map(inner, v))));
}

TEST_CASE("simd: ap does not exist here -- the invoke-interface proof") {
    // vec<callable> is not a type, so one-step contextual application
    // cannot be spelled: the derived ap's constraint is a clean false for
    // every nameable operand. This is the case that makes invoke the
    // user-facing interface -- ap remains a fine basis elsewhere, but an
    // ap-shaped interface would lock this domain out entirely.
    using Map = bt::remove_cvref_t<decltype(bt::applicative_typeclass<vec4>)>;
    STATIC_REQUIRE_FALSE(bt::test::has_apply_form<Map, vec4, vec4>);
    SUCCEED("std::simd::basic_vec participates through pure + invoke alone");
}

#else // no std::simd in this configuration

#include <catch2/catch_test_macros.hpp>

TEST_CASE("simd: std::simd (P1928, C++26) unavailable in this configuration") {
    SUCCEED("simd applicative tests skipped: <simd> or C++26 not available");
}

#endif
