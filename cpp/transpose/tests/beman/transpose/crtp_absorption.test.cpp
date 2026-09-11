// tests/beman/transpose/crtp_absorption.test.cpp                     -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

// Stage crtp-absorption (docs/transpose-grading-plan.md#crtp-absorption).
//
// The claim under test is an ERGONOMICS invariant, not a behavioural one:
// registering a kind must stay "a couple of functions", and an instance that
// has never heard of grades must keep working verbatim, treated as uniformly
// ∅-graded (docs/decisions.md#grade-machinery-home). The sentinel for that
// decision is that a typeclass instance never has to declare grade
// participation -- so the test that matters is one whose instance says
// nothing about grades at all and still gets the whole surface.

#include <beman/transpose/apply.hpp>

#include <beman/transpose/error_set.hpp>
#include <beman/transpose/grade.hpp>
#include <beman/transpose/monad.hpp>
#include <beman/transpose/sequence.hpp>
#include <beman/transpose/transpose.hpp>
#include <beman/transpose/traverse.hpp>

#include <catch2/catch_test_macros.hpp>

#include <expected>
#include <functional>
#include <optional>
#include <type_traits>
#include <utility>
#include <vector>

namespace bt = beman::transpose;

namespace beman_transpose_absorption_probes {

struct alpha {
    int value{};
};
struct beta {
    int value{};
};

/** A minimal context: one value, no failure mode, no grade awareness. */
template <class VALUE_TYPE>
struct boxed {
    using value_type = VALUE_TYPE;

    VALUE_TYPE value{};

    friend auto operator==(const boxed &, const boxed &) -> bool = default;
};

} // namespace beman_transpose_absorption_probes

namespace probes = beman_transpose_absorption_probes;

using probes::alpha;
using probes::beta;
using probes::boxed;

namespace beman::transpose {

// THE WHOLE REGISTRATION. Two functions, no mention of grades, no opt-in,
// no declaration of participation. If a later stage makes this insufficient,
// the factoring has leaked.
template <class VALUE_TYPE>
struct BoxedApplicativeImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value) -> boxed<remove_cvref_t<VALUE>> {
        return boxed<remove_cvref_t<VALUE>>{std::forward<VALUE>(value)};
    }

    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function, const boxed<FIRST> &first,
                const boxed<REST> &...rest)
        -> boxed<remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>> {
        using Result = remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>;
        return boxed<Result>{std::invoke(function, first.value, rest.value...)};
    }
};

template <class VALUE_TYPE>
struct BoxedApplicativeMap : Applicative<BoxedApplicativeImpl<VALUE_TYPE>> {
    using BoxedApplicativeImpl<VALUE_TYPE>::invoke;
    using BoxedApplicativeImpl<VALUE_TYPE>::pure;
};

template <class VALUE_TYPE>
inline constexpr auto applicative_typeclass<boxed<VALUE_TYPE>> =
    BoxedApplicativeMap<VALUE_TYPE>{};

} // namespace beman::transpose

namespace {

using set_a = bt::error_set<alpha>;
using set_ab = bt::error_set<alpha, beta>;

// =========================================================================
// 1. The zero-grade-awareness instance is ∅-graded and works verbatim.
// =========================================================================

static_assert(std::is_same_v<bt::grade_of_t<boxed<int>>, bt::unit_grade>);
static_assert(!bt::graded_context<boxed<int>>);

// It deduces exactly what an ungraded instance should, through the front door.
auto boxed_of(const int &x) -> boxed<int> { return boxed<int>{x}; }

static_assert(
    std::is_same_v<decltype(bt::traverse(
                       boxed_of, std::declval<const std::vector<int> &>())),
                   boxed<std::vector<int>>>);

// =========================================================================
// 2. subsume is present on every instance for model grades.
//
// The instance did not ask for this member and cannot tell it is there. The
// framework sentinel itself is not a grade and is not a subsumption target.
// =========================================================================

// A ∅-graded carrier cannot be widened to a grade its algebra does not
// license... except that ∅ subsumes into everything, which is the promotion
// case below. What is NOT available is narrowing.
template <class GRADE, class CARRIER>
concept subsumable =
    requires(const CARRIER &value) { bt::grade_subsume<GRADE>(value); };

static_assert(subsumable<set_ab, std::expected<int, set_a>>);
static_assert(!subsumable<set_a, std::expected<int, set_ab>>);

// =========================================================================
// 3. Promotion of bare values at ∅ is subsumption, not a separate mechanism.
//
// docs/decisions.md#empty-grade-spelling: the coercion out of ∅ is
// expected's existing converting constructor from T. The standard already
// implements η, so the framework contributes nothing but the constraint.
// =========================================================================

static_assert(std::is_same_v<
              decltype(bt::grade_subsume<set_ab>(std::declval<const int &>())),
              std::expected<int, set_ab>>);
static_assert(
    std::is_same_v<decltype(bt::grade_subsume<set_ab>(
                       std::declval<const std::expected<int, set_a> &>())),
                   std::expected<int, set_ab>>);

// Promotion at the model bottom is the identity, and in particular does NOT
// manufacture expected<int, error_set<>> -- the sentinel again, now at the
// value level.
static_assert(std::is_same_v<decltype(bt::grade_subsume<bt::error_set<>>(
                                 std::declval<const int &>())),
                             int>);

} // namespace

TEST_CASE("crtp-absorption: a two-function registration needs no grade code") {
    const auto &app = bt::applicative_typeclass<boxed<int>>;

    REQUIRE(app.pure(4) == boxed<int>{4});
    REQUIRE(app.invoke([](int a, int b) { return a + b; }, boxed<int>{2},
                       boxed<int>{3}) == boxed<int>{5});
    REQUIRE(app.map([](int x) { return x * 2; }, boxed<int>{6}) ==
            boxed<int>{12});

    auto traversed = bt::traverse(boxed_of, std::vector<int>{1, 2, 3});
    REQUIRE(traversed == boxed<std::vector<int>>{{1, 2, 3}});
}

TEST_CASE("crtp-absorption: subsume widens a graded carrier") {
    std::expected<int, set_a> narrow{7};
    auto wide = bt::grade_subsume<set_ab>(narrow);

    static_assert(std::is_same_v<decltype(wide), std::expected<int, set_ab>>);
    REQUIRE(wide.has_value());
    REQUIRE(*wide == 7);

    std::expected<int, set_a> failed{std::unexpect, set_a{alpha{3}}};
    auto widened_error = bt::grade_subsume<set_ab>(failed);
    REQUIRE_FALSE(widened_error.has_value());
    REQUIRE(widened_error.error().holds<alpha>());
}

TEST_CASE("crtp-absorption: promotion of a bare value at the empty grade") {
    auto promoted = bt::grade_subsume<set_ab>(41);

    static_assert(
        std::is_same_v<decltype(promoted), std::expected<int, set_ab>>);
    REQUIRE(promoted.has_value());
    REQUIRE(*promoted == 41);
}

TEST_CASE("crtp-absorption: ap derived from the bind basis") {
    const auto &monad = bt::monad_typeclass<std::optional<int>>;

    auto doubler = [](const int &x) { return x * 2; };
    std::optional<decltype(doubler)> callable{doubler};

    REQUIRE(monad.ap(callable, std::optional<int>{21}) ==
            std::optional<int>{42});
    REQUIRE(monad.ap(callable, std::optional<int>{}) == std::optional<int>{});

    std::optional<decltype(doubler)> absent{};
    REQUIRE(monad.ap(absent, std::optional<int>{21}) == std::optional<int>{});
}

TEST_CASE("crtp-absorption: derived ap agrees with the applicative's own") {
    const auto &monad = bt::monad_typeclass<std::optional<int>>;
    const auto &applicative = bt::applicative_typeclass<std::optional<int>>;

    auto doubler = [](const int &x) { return x * 2; };
    std::optional<decltype(doubler)> callable{doubler};

    REQUIRE(monad.ap(callable, std::optional<int>{21}) ==
            applicative.ap(callable, std::optional<int>{21}));
}
