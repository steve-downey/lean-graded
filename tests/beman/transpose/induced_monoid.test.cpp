// tests/beman/transpose/induced_monoid.test.cpp                     -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/induced_monoid.hpp>

#include <beman/transpose/apply.hpp>
#include <beman/transpose/monad.hpp>
#include <beman/transpose/monoid.hpp>

#include <catch2/catch_test_macros.hpp>

#include <array>
#include <optional>

namespace bt = beman::transpose;

namespace {

// Sentinel: the raw carriers these monoids are induced over do not
// themselves gain a Monoid. "Named and unregistered" means operationally
// that this concept stays false for them.
template <class T>
concept has_monoid = requires { bt::monoid_v<T>.identity(); };

static_assert(!has_monoid<std::optional<int>>);
static_assert(!has_monoid<std::optional<bt::Sum<int>>>);

} // namespace

// ============================================================================
// KleisliEndo: the Kleisli endomorphism monoid over std::optional<int>.
// Identity is pure, combine is Kleisli composition (>=>). The Kleisli-form
// monad laws (pure is the two-sided unit of >=>, and >=> is associative) are
// exactly the three monoid laws checked below, applied "as functions": two
// arrows are compared by applying both to the same inputs and comparing
// results, since the erased carrier holds a std::function and has no
// operator==.
// ============================================================================

namespace {

using MonadObj = bt::OptionalMonadMap<int>;
using Endo = bt::KleisliEndo<MonadObj, int>;

// Arrows exercising both the engaged and disengaged branches of the
// underlying std::optional context.
auto increment_below_100(const int &a) -> std::optional<int> {
    return a < 100 ? std::optional<int>{a + 1} : std::optional<int>{};
}

auto doubled(const int &a) -> std::optional<int> {
    return std::optional<int>{a * 2};
}

auto decrement_above_zero(const int &a) -> std::optional<int> {
    return a > 0 ? std::optional<int>{a - 1} : std::optional<int>{};
}

constexpr std::array sample_inputs{-3, 0, 1, 50, 99, 100};

// Compares two arrows "as functions": applies both to every sample input and
// checks that the results agree.
template <class F, class G>
auto agree_on_samples(const F &f, const G &g) -> bool {
    for (int x : sample_inputs) {
        if (f(x) != g(x)) {
            return false;
        }
    }
    return true;
}

} // namespace

TEST_CASE("induced_monoid: KleisliEndo identity is pure") {
    auto id = bt::monoid_v<Endo>.identity();
    for (int x : sample_inputs) {
        REQUIRE(id(x) == std::optional<int>{x});
    }
}

TEST_CASE("induced_monoid: KleisliEndo left identity -- combine(pure, f) "
          "agrees with f") {
    Endo f{increment_below_100};
    auto id = bt::monoid_v<Endo>.identity();
    auto composed = bt::monoid_v<Endo>.combine(id, f);
    REQUIRE(agree_on_samples(composed, f));
}

TEST_CASE("induced_monoid: KleisliEndo right identity -- combine(f, pure) "
          "agrees with f") {
    Endo f{increment_below_100};
    auto id = bt::monoid_v<Endo>.identity();
    auto composed = bt::monoid_v<Endo>.combine(f, id);
    REQUIRE(agree_on_samples(composed, f));
}

TEST_CASE("induced_monoid: KleisliEndo combine is >=> -- Kleisli forward "
          "composition") {
    Endo f{increment_below_100};
    Endo g{doubled};
    auto composed = bt::monoid_v<Endo>.combine(f, g);
    for (int x : sample_inputs) {
        auto expected = bt::mbind(f(x), doubled);
        REQUIRE(composed(x) == expected);
    }
}

TEST_CASE("induced_monoid: KleisliEndo associativity -- the Kleisli-form "
          "monad law") {
    Endo f{increment_below_100};
    Endo g{doubled};
    Endo h{decrement_above_zero};

    auto left = bt::monoid_v<Endo>.combine(bt::monoid_v<Endo>.combine(f, g), h);
    auto right =
        bt::monoid_v<Endo>.combine(f, bt::monoid_v<Endo>.combine(g, h));

    REQUIRE(agree_on_samples(left, right));
}

// ============================================================================
// LiftedMonoid: the applicative-lifted monoid, F<A> from a Monoid<A>. Lifted
// here over std::optional<Sum<int>> -- Sum<int> supplies the element monoid,
// std::optional<Sum<int>> is the F<A> that becomes a monoid.
// ============================================================================

namespace {

using ApplicativeObj = bt::OptionalApplicativeMap<bt::Sum<int>>;
using Lifted = bt::LiftedMonoid<ApplicativeObj, std::optional<bt::Sum<int>>>;

// Checks the three monoid laws for a handful of values of a carrier `M`,
// including a disengaged operand -- the same shape as monoid.test.cpp's
// local law-checker, specialized to LiftedMonoid's equality.
auto check_lifted_laws(const Lifted &a, const Lifted &b, const Lifted &c)
    -> bool {
    const auto e = bt::monoid_v<Lifted>.identity();
    const bool left_identity = bt::monoid_v<Lifted>.combine(e, a) == a;
    const bool right_identity = bt::monoid_v<Lifted>.combine(a, e) == a;
    const bool associative =
        bt::monoid_v<Lifted>.combine(bt::monoid_v<Lifted>.combine(a, b), c) ==
        bt::monoid_v<Lifted>.combine(a, bt::monoid_v<Lifted>.combine(b, c));
    return left_identity && right_identity && associative;
}

} // namespace

TEST_CASE("induced_monoid: LiftedMonoid identity is pure(monoid_v<A>."
          "identity())") {
    REQUIRE(bt::monoid_v<Lifted>.identity().d_value ==
            std::optional<bt::Sum<int>>{bt::Sum<int>{0}});
}

TEST_CASE("induced_monoid: LiftedMonoid combine is invoke(combine_A) over "
          "engaged operands") {
    Lifted x{std::optional<bt::Sum<int>>{bt::Sum<int>{3}}};
    Lifted y{std::optional<bt::Sum<int>>{bt::Sum<int>{4}}};
    REQUIRE(bt::monoid_v<Lifted>.combine(x, y).d_value ==
            std::optional<bt::Sum<int>>{bt::Sum<int>{7}});
}

TEST_CASE("induced_monoid: LiftedMonoid combine propagates a disengaged "
          "operand") {
    Lifted engaged{std::optional<bt::Sum<int>>{bt::Sum<int>{3}}};
    Lifted disengaged{std::optional<bt::Sum<int>>{}};
    REQUIRE(bt::monoid_v<Lifted>.combine(engaged, disengaged).d_value ==
            std::optional<bt::Sum<int>>{});
    REQUIRE(bt::monoid_v<Lifted>.combine(disengaged, engaged).d_value ==
            std::optional<bt::Sum<int>>{});
}

TEST_CASE("induced_monoid: LiftedMonoid satisfies the monoid laws, engaged "
          "operands") {
    Lifted a{std::optional<bt::Sum<int>>{bt::Sum<int>{2}}};
    Lifted b{std::optional<bt::Sum<int>>{bt::Sum<int>{3}}};
    Lifted c{std::optional<bt::Sum<int>>{bt::Sum<int>{5}}};
    REQUIRE(check_lifted_laws(a, b, c));
}

TEST_CASE("induced_monoid: LiftedMonoid satisfies the monoid laws with a "
          "disengaged operand") {
    Lifted a{std::optional<bt::Sum<int>>{bt::Sum<int>{2}}};
    Lifted b{std::optional<bt::Sum<int>>{}};
    Lifted c{std::optional<bt::Sum<int>>{bt::Sum<int>{5}}};
    REQUIRE(check_lifted_laws(a, b, c));
}
