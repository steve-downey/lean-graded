// tests/beman/transpose/monoid.test.cpp                              -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/monoid.hpp>

#include <catch2/catch_test_macros.hpp>

#include <limits>
#include <string>
#include <vector>

namespace bt = beman::transpose;

namespace {

// Checks the three monoid laws for a handful of values of a carrier `M`.
// Local to this test file: it speaks plain monoid vocabulary, not the graded
// vocabulary of laws.hpp, so it does not belong there.
template <class M>
constexpr auto check_monoid_laws(const M &a, const M &b, const M &c) -> bool {
    const auto e = bt::monoid_v<M>.identity();
    const bool left_identity = bt::monoid_v<M>.combine(e, a) == a;
    const bool right_identity = bt::monoid_v<M>.combine(a, e) == a;
    const bool associative =
        bt::monoid_v<M>.combine(bt::monoid_v<M>.combine(a, b), c) ==
        bt::monoid_v<M>.combine(a, bt::monoid_v<M>.combine(b, c));
    return left_identity && right_identity && associative;
}

static_assert(check_monoid_laws(bt::Sum<int>{2}, bt::Sum<int>{3},
                                bt::Sum<int>{5}));
static_assert(check_monoid_laws(bt::Product<int>{2}, bt::Product<int>{3},
                                bt::Product<int>{5}));
static_assert(check_monoid_laws(bt::Max<int>{2}, bt::Max<int>{3},
                                bt::Max<int>{5}));
static_assert(check_monoid_laws(bt::Min<int>{2}, bt::Min<int>{3},
                                bt::Min<int>{5}));
static_assert(check_monoid_laws(bt::Any{false}, bt::Any{true}, bt::Any{false}));
static_assert(check_monoid_laws(bt::All{true}, bt::All{false}, bt::All{true}));

// Sentinel: no bare-numeric Monoid is registered, so the choice among
// addition, product, max, min, ... must be spelled by a named carrier.
// A future re-registration of Monoid<int> (or long, or size_t) fails these
// static_asserts rather than silently restoring the old, unnamed default.
// Probed on the specialization itself, never through monoid_v: naming
// monoid_v<T> declares a variable of the undefined type Monoid<T>, and that
// failure is outside the requires-expression's immediate context -- a hard
// error, not `false`.
template <class T>
concept has_monoid = requires {
    sizeof(beman::transpose::Monoid<T>);
} && requires(const beman::transpose::Monoid<T> &m) { m.identity(); };

static_assert(!has_monoid<int>);
static_assert(!has_monoid<long>);
static_assert(!has_monoid<std::size_t>);
static_assert(has_monoid<bt::Sum<int>>);

} // namespace

TEST_CASE("monoid: int additive identity and combine via Sum") {
    REQUIRE(bt::monoid_identity<bt::Sum<int>>() == bt::Sum<int>{0});
    REQUIRE(bt::monoid_combine(bt::Sum<int>{3}, bt::Sum<int>{4}) ==
            bt::Sum<int>{7});
}

TEST_CASE("monoid: string concatenation") {
    REQUIRE(bt::monoid_identity<std::string>().empty());
    REQUIRE(bt::monoid_combine(std::string{"ab"}, std::string{"cd"}) == "abcd");
}

TEST_CASE("monoid: vector concatenation") {
    std::vector<int> lhs{1, 2};
    std::vector<int> rhs{3, 4};
    REQUIRE(bt::monoid_combine(lhs, rhs) == std::vector<int>{1, 2, 3, 4});
    REQUIRE(bt::monoid_identity<std::vector<int>>().empty());
}

TEST_CASE("monoid: Count combines by addition") {
    auto combined = bt::monoid_combine(bt::Count{2}, bt::Count{5});
    REQUIRE(combined == bt::Count{7});
}

TEST_CASE("monoid: Sum combines by addition") {
    using S = bt::Sum<int>;
    REQUIRE(check_monoid_laws(S{2}, S{3}, S{5}));
    REQUIRE(bt::monoid_v<S>.identity() == S{0});
    REQUIRE(bt::monoid_v<S>.combine(S{2}, S{5}) == S{7});
}

TEST_CASE("monoid: Product combines by multiplication") {
    using P = bt::Product<int>;
    REQUIRE(check_monoid_laws(P{2}, P{3}, P{5}));
    REQUIRE(bt::monoid_v<P>.identity() == P{1});
    REQUIRE(bt::monoid_v<P>.combine(P{2}, P{5}) == P{10});
}

TEST_CASE("monoid: Max combines by taking the larger value") {
    using M = bt::Max<int>;
    REQUIRE(check_monoid_laws(M{2}, M{3}, M{5}));
    REQUIRE(bt::monoid_v<M>.combine(M{2}, M{5}) == M{5});
}

TEST_CASE("monoid: Min combines by taking the smaller value") {
    using M = bt::Min<int>;
    REQUIRE(check_monoid_laws(M{2}, M{3}, M{5}));
    REQUIRE(bt::monoid_v<M>.combine(M{2}, M{5}) == M{2});
}

TEST_CASE("monoid: Max identity is the saturating lower bound of T") {
    REQUIRE(bt::monoid_v<bt::Max<int>>.identity().d_value ==
            std::numeric_limits<int>::lowest());
    REQUIRE(bt::monoid_v<bt::Max<double>>.identity().d_value ==
            -std::numeric_limits<double>::infinity());
}

TEST_CASE("monoid: Min identity is the saturating upper bound of T") {
    REQUIRE(bt::monoid_v<bt::Min<int>>.identity().d_value ==
            std::numeric_limits<int>::max());
    REQUIRE(bt::monoid_v<bt::Min<double>>.identity().d_value ==
            std::numeric_limits<double>::infinity());
}

TEST_CASE("monoid: Any combines by logical or") {
    REQUIRE(check_monoid_laws(bt::Any{false}, bt::Any{true}, bt::Any{false}));
    REQUIRE(bt::monoid_v<bt::Any>.identity() == bt::Any{false});
    REQUIRE(bt::monoid_v<bt::Any>.combine(bt::Any{false}, bt::Any{true}) ==
            bt::Any{true});
}

TEST_CASE("monoid: All combines by logical and") {
    REQUIRE(check_monoid_laws(bt::All{true}, bt::All{false}, bt::All{true}));
    REQUIRE(bt::monoid_v<bt::All>.identity() == bt::All{true});
    REQUIRE(bt::monoid_v<bt::All>.combine(bt::All{false}, bt::All{true}) ==
            bt::All{false});
}
