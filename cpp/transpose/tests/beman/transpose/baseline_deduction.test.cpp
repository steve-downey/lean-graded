// tests/beman/transpose/baseline_deduction.test.cpp                  -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

// GOLDEN DEDUCTION TESTS -- stage baseline-capture of the grading plan
// (docs/transpose-grading-plan.md#baseline-capture).
//
// EVERY assertion in this file is a golden: it pins the EXACT type the
// library deduces, and no remaining stage will legitimately change it. What
// makes a golden gold is precisely that nothing in the plan is due to move
// it. The additive-compatibility claim of
// docs/decisions.md#grading-footprint -- "for any input combination that
// deduces a type today, the graded framework deduces the same type" -- is
// proved by keeping them green, not by argument. A golden that fails is a
// regression. Never update one to make a stage pass; that inverts the sensor
// (divergence protocol rule 4).
//
// Assertions that a named stage IS due to reverse do not belong here. They
// live in their own translation unit with a stated expiry, because a golden
// with a scheduled flip is a to-do wearing a sensor's clothes and teaches the
// reader that a red build is routine. See
// docs/decisions.md#golden-vs-scheduled-assertions. There is no such file at
// present: the mixing frontier was the only scheduled block, stage
// graded-deduction retired it, and section 9 below is what it became.
//
// Everything here lives in unevaluated context, so the file is a
// compile-time artifact: if it compiles, the assertions hold.

#include <beman/transpose/transpose.hpp>

#include "test_support.hpp"

#include <catch2/catch_test_macros.hpp>

#include <array>
#include <expected>
#include <ios>
#include <optional>
#include <system_error>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

namespace bt = beman::transpose;

namespace {

// -- Registration probes ---------------------------------------------------
// Availability is a NAMED CONCEPT on purpose, matching test_support.hpp: a
// bare requires-expression at block scope hard-errors on an invalid
// expression instead of yielding false ([expr.prim.req]). An unregistered
// typeclass lookup yields std::false_type; a registered one yields the map.

template <class T>
concept applicative_registered =
    !std::is_same_v<std::remove_const_t<decltype(bt::applicative_typeclass<T>)>,
                    std::false_type>;

template <class T>
concept monad_registered =
    !std::is_same_v<std::remove_const_t<decltype(bt::monad_typeclass<T>)>,
                    std::false_type>;

template <class T>
concept functor_registered =
    !std::is_same_v<std::remove_const_t<decltype(bt::functor_typeclass<T>)>,
                    std::false_type>;

template <class T>
concept traversable_registered =
    !std::is_same_v<std::remove_const_t<decltype(bt::traversable_typeclass<T>)>,
                    std::false_type>;

// -- Probe callables -------------------------------------------------------
// Defined, not merely declared: deducing a return type instantiates the
// template body, and an undefined callee would fail to link.
//
// [[maybe_unused]] because every use below is unevaluated: an internal-linkage
// function that is named only inside decltype is never odr-used, so no
// definition is emitted and clang's -Wunneeded-internal-declaration fires. The
// attribute states the intent -- the body exists to be linkable if a deduction
// ever needs it, not because this TU calls it.

[[maybe_unused]] constexpr auto to_double(const int &x) -> double {
    return x * 2.0;
}
[[maybe_unused]] constexpr auto add(const int &x, const int &y) -> int {
    return x + y;
}

[[maybe_unused]] auto opt_of(const int &x) -> std::optional<int> {
    return std::optional<int>{x};
}
[[maybe_unused]] auto opt_double_of(const int &x) -> std::optional<double> {
    return std::optional<double>{static_cast<double>(x)};
}
[[maybe_unused]] auto sender_of(const int &x) -> bt::sender<int> {
    return bt::sender<int>::ready(x);
}
[[maybe_unused]] auto zip_of(const int &x) -> bt::zip_list<int> {
    return bt::zip_list<int>::repeat(x);
}

/** A callable held *inside* a context, to exercise the derived ap basis. */
struct doubler {
    constexpr auto operator()(const int &x) const -> double { return x * 2.0; }
};

// Shorthand for the operands, all as const lvalues.
using opt_int = std::optional<int>;
using opt_double = std::optional<double>;
using vec_int = std::vector<int>;

// =========================================================================
// 1. Applicative over std::optional -- the flagship invoke-native instance.
// =========================================================================

inline constexpr const auto &opt_app = bt::applicative_typeclass<opt_int>;

static_assert(std::is_same_v<decltype(opt_app.pure(std::declval<int>())),
                             std::optional<int>>);
static_assert(std::is_same_v<decltype(opt_app.lift(std::declval<int>())),
                             std::optional<int>>);
static_assert(
    std::is_same_v<decltype(opt_app.invoke(add, std::declval<const opt_int &>(),
                                           std::declval<const opt_int &>())),
                   std::optional<int>>);
static_assert(std::is_same_v<
              decltype(opt_app.map(to_double, std::declval<const opt_int &>())),
              std::optional<double>>);
static_assert(std::is_same_v<
              decltype(opt_app.zip_with(add, std::declval<const opt_int &>(),
                                        std::declval<const opt_int &>())),
              std::optional<int>>);
static_assert(std::is_same_v<decltype(opt_app.discard_first(
                                 std::declval<const opt_int &>(),
                                 std::declval<const opt_double &>())),
                             std::optional<double>>);
static_assert(std::is_same_v<decltype(opt_app.discard_second(
                                 std::declval<const opt_int &>(),
                                 std::declval<const opt_double &>())),
                             std::optional<int>>);

// The derived ap basis: available exactly because optional can hold a
// callable. ap(cf, cx) = invoke(applicative_eval, cf, cx).
static_assert(std::is_same_v<decltype(opt_app.ap(
                                 std::declval<const std::optional<doubler> &>(),
                                 std::declval<const opt_int &>())),
                             std::optional<double>>);

// =========================================================================
// 2. Monad over std::optional -- bind basis, invoke synthesized.
// =========================================================================

inline constexpr const auto &opt_monad = bt::monad_typeclass<opt_int>;

static_assert(
    std::is_same_v<decltype(opt_monad.bind(std::declval<const opt_int &>(),
                                           opt_double_of)),
                   std::optional<double>>);
static_assert(std::is_same_v<
              decltype(opt_monad.invoke(add, std::declval<const opt_int &>(),
                                        std::declval<const opt_int &>())),
              std::optional<int>>);
static_assert(std::is_same_v<decltype(bt::mbind(std::declval<const opt_int &>(),
                                                opt_double_of)),
                             std::optional<double>>);
static_assert(
    std::is_same_v<
        decltype(bt::join(std::declval<const std::optional<opt_int> &>())),
        std::optional<int>>);

// =========================================================================
// 3. Functor over std::optional and std::vector.
// =========================================================================

static_assert(std::is_same_v<decltype(bt::functor_typeclass<opt_int>.fmap(
                                 to_double, std::declval<const opt_int &>())),
                             std::optional<double>>);
static_assert(std::is_same_v<decltype(bt::functor_typeclass<vec_int>.fmap(
                                 to_double, std::declval<const vec_int &>())),
                             std::vector<double>>);
static_assert(std::is_same_v<decltype(bt::functor_typeclass<opt_int>.replace(
                                 std::declval<const opt_int &>(),
                                 std::declval<double>())),
                             std::optional<double>>);

// =========================================================================
// 4. Traversable over std::vector, through each shipped applicative.
//    These are the three front-door results of Paper A's motivating
//    domains, and the shape of every compatibility claim downstream.
// =========================================================================

static_assert(std::is_same_v<
              decltype(bt::traverse(opt_of, std::declval<const vec_int &>())),
              std::optional<std::vector<int>>>);
static_assert(
    std::is_same_v<decltype(bt::traverse(opt_double_of,
                                         std::declval<const vec_int &>())),
                   std::optional<std::vector<double>>>);
static_assert(std::is_same_v<decltype(bt::traverse(
                                 sender_of, std::declval<const vec_int &>())),
                             bt::sender<std::vector<int>>>);
static_assert(std::is_same_v<
              decltype(bt::traverse(zip_of, std::declval<const vec_int &>())),
              bt::zip_list<std::vector<int>>>);

// transpose is traverse(identity): structure<context<T>> ->
// context<structure<T>>
static_assert(std::is_same_v<decltype(bt::transpose(
                                 std::declval<const std::vector<opt_int> &>())),
                             std::optional<std::vector<int>>>);
static_assert(
    std::is_same_v<decltype(bt::transpose(
                       std::declval<const std::vector<bt::sender<int>> &>())),
                   bt::sender<std::vector<int>>>);

// The derived object operations deduce identically to the free functions.
static_assert(
    std::is_same_v<decltype(bt::traversable_typeclass<vec_int>.for_each(
                       std::declval<const vec_int &>(), opt_of)),
                   std::optional<std::vector<int>>>);

// =========================================================================
// 5. Traversable over the test Identity context.
// =========================================================================

using ident_int = bt::test::Identity<int>;

static_assert(
    std::is_same_v<decltype(bt::traversable_typeclass<ident_int>.for_each(
                       std::declval<const ident_int &>(), opt_of)),
                   std::optional<bt::test::Identity<int>>>);

// =========================================================================
// 6. Positional applicatives: std::array and the SoA/AoS tuple transpose.
// =========================================================================

using arr3 = std::array<int, 3>;

static_assert(std::is_same_v<decltype(bt::applicative_typeclass<arr3>.invoke(
                                 add, std::declval<const arr3 &>(),
                                 std::declval<const arr3 &>())),
                             std::array<int, 3>>);
static_assert(
    std::is_same_v<decltype(bt::transpose_tuple(
                       std::declval<const std::tuple<
                           std::array<int, 2>, std::array<double, 2>> &>())),
                   std::array<std::tuple<int, double>, 2>>);

// =========================================================================
// 7. Registration invariants.
//
// Which types are contexts, and which must never become one. No stage in
// the plan changes any of these, so a failure here is a regression.
//
// (Two of them did read `!registered` at stage baseline-capture, when
// expected appeared nowhere in the library. Stage expected-instance
// registered it, and that flip was scheduled rather than detected -- see
// section 9 on why such assertions do not belong among the goldens.)
// =========================================================================

using exp_int = std::expected<int, std::errc>;

static_assert(applicative_registered<exp_int>);
static_assert(monad_registered<exp_int>);

// Functor is deliberately NOT registered for expected: no stage in the plan
// calls for it, and the Applicative and Monad instances do not need it. If
// this flips, scope widened without a decision behind it.
static_assert(!functor_registered<exp_int>);

// Bare values carry no registration, and must never acquire one. Under
// docs/decisions.md#empty-grade-spelling bare `T` IS the empty grade, so the
// promotion of bare values at grade zero (stage crtp-absorption) has to
// arrive WITHOUT registering `int` as a context. This is the load-bearing
// negative in the file: it holds for the whole run, and stage
// crtp-absorption is the one most likely to break it by taking the easy
// route. It is a golden, not a milestone.
static_assert(!applicative_registered<int>);
static_assert(!monad_registered<int>);

// The STRUCTURE side is already ready for expected; only the CONTEXT side is
// missing. A vector of expected is a registered traversable today -- it just
// has nothing to transpose into.
static_assert(traversable_registered<std::vector<exp_int>>);
static_assert(traversable_registered<vec_int>);

// The element-extraction trait already handles expected via its nested
// value_type, with no specialization needed. Stage grade-concept depends on
// this holding.
static_assert(std::is_same_v<bt::applicative_value_t<exp_int>, int>);
static_assert(std::is_same_v<bt::applicative_value_t<opt_int>, int>);

// -- Contexts that ARE registered today, pinned as the complement. ---------
static_assert(applicative_registered<opt_int>);
static_assert(applicative_registered<bt::sender<int>>);
static_assert(applicative_registered<bt::zip_list<int>>);
static_assert(applicative_registered<arr3>);
static_assert(applicative_registered<ident_int>);
static_assert(monad_registered<opt_int>);
static_assert(functor_registered<opt_int>);
static_assert(functor_registered<vec_int>);

// =========================================================================
// 8. Stage expected-instance -- the ungraded before-state.
//
// These are the deductions the graded framework must reproduce
// character-for-character. Read them as the statement that
// docs/decisions.md#grading-footprint's no-spontaneous-singletons corollary
// is measurable: every result below is `expected<T, E>` with a bare error
// type, and not one of them is `expected<T, error_set<E>>`. A later stage
// that turns any of these into a singleton error_set has manufactured a
// grade out of an unmixed pipeline, which is the thing the corollary forbids.
// =========================================================================

[[maybe_unused]] auto exp_of(const int &x) -> exp_int { return exp_int{x}; }
[[maybe_unused]] auto exp_double_of(const int &x)
    -> std::expected<double, std::errc> {
    return std::expected<double, std::errc>{static_cast<double>(x)};
}

inline constexpr const auto &exp_app = bt::applicative_typeclass<exp_int>;
inline constexpr const auto &exp_monad = bt::monad_typeclass<exp_int>;

static_assert(std::is_same_v<decltype(exp_app.pure(std::declval<int>())),
                             std::expected<int, std::errc>>);
static_assert(
    std::is_same_v<decltype(exp_app.invoke(add, std::declval<const exp_int &>(),
                                           std::declval<const exp_int &>())),
                   std::expected<int, std::errc>>);
static_assert(std::is_same_v<
              decltype(exp_app.map(to_double, std::declval<const exp_int &>())),
              std::expected<double, std::errc>>);
static_assert(std::is_same_v<
              decltype(exp_app.discard_first(std::declval<const exp_int &>(),
                                             std::declval<const exp_int &>())),
              std::expected<int, std::errc>>);
static_assert(
    std::is_same_v<decltype(exp_monad.bind(std::declval<const exp_int &>(),
                                           exp_double_of)),
                   std::expected<double, std::errc>>);
static_assert(std::is_same_v<decltype(bt::mbind(std::declval<const exp_int &>(),
                                                exp_double_of)),
                             std::expected<double, std::errc>>);
static_assert(std::is_same_v<
              decltype(bt::join(
                  std::declval<const std::expected<exp_int, std::errc> &>())),
              std::expected<int, std::errc>>);
static_assert(std::is_same_v<
              decltype(bt::traverse(exp_of, std::declval<const vec_int &>())),
              std::expected<std::vector<int>, std::errc>>);
static_assert(std::is_same_v<decltype(bt::transpose(
                                 std::declval<const std::vector<exp_int> &>())),
                             std::expected<std::vector<int>, std::errc>>);

// =========================================================================
// 9. Graded deduction at a mixing point. Golden as of stage
//    graded-deduction, which promoted these from the scheduled block that
//    used to assert the opposite (current_state.test.cpp, now retired).
//
// This is the ONE place grading changes behaviour, and it only claims
// territory that was ill-formed before: none of the combinations below
// deduced anything at all until this stage. Nothing that already deduced a
// type deduces a different one -- which is what sections 1 to 8 are for.
// =========================================================================

using exp_io = std::expected<int, std::io_errc>;
using mixed_errors = bt::error_set<std::errc, std::io_errc>;

[[maybe_unused]] auto exp_io_of(const int &x)
    -> std::expected<double, std::io_errc> {
    return std::expected<double, std::io_errc>{static_cast<double>(x)};
}

// Two different error types join into the error_set of both.
static_assert(
    std::is_same_v<decltype(exp_app.invoke(add, std::declval<const exp_int &>(),
                                           std::declval<const exp_io &>())),
                   std::expected<int, mixed_errors>>);

// Grades are order-blind: ∪ commutes, so the operand order cannot change the
// deduced grade. (It still fixes which error is OBSERVED, which is why the
// traversal order is specified normatively rather than left to the types.)
static_assert(
    std::is_same_v<decltype(exp_app.invoke(add, std::declval<const exp_io &>(),
                                           std::declval<const exp_int &>())),
                   std::expected<int, mixed_errors>>);

// Sequencing joins too: a continuation raising a different error widens the
// result.
static_assert(std::is_same_v<decltype(exp_monad.bind(
                                 std::declval<const exp_int &>(), exp_io_of)),
                             std::expected<double, mixed_errors>>);

// An operand already carrying an error_set absorbs the other side's error
// rather than nesting a set inside a set.
static_assert(
    std::is_same_v<
        decltype(bt::applicative_typeclass<
                     std::expected<int, bt::error_set<std::errc>>>
                     .invoke(add,
                             std::declval<const std::expected<
                                 int, bt::error_set<std::errc>> &>(),
                             std::declval<const exp_io &>())),
        std::expected<int, mixed_errors>>);

// LAZY JOIN. A bare operand is ∅-graded: it is promoted inside the framework
// and leaves no trace, so mixing it with a graded operand does NOT
// manufacture a singleton error_set. This is the no-spontaneous-singletons
// corollary at the one place it could plausibly break.
static_assert(
    std::is_same_v<decltype(exp_app.invoke(add, std::declval<const exp_int &>(),
                                           std::declval<const int &>())),
                   std::expected<int, std::errc>>);
static_assert(
    std::is_same_v<decltype(exp_app.invoke(add, std::declval<const int &>(),
                                           std::declval<const exp_int &>())),
                   std::expected<int, std::errc>>);

// And the same for two operands that agree on an error_set: carried
// verbatim, not re-wrapped.
static_assert(
    std::is_same_v<
        decltype(bt::applicative_typeclass<
                     std::expected<int, bt::error_set<std::errc>>>
                     .invoke(add,
                             std::declval<const std::expected<
                                 int, bt::error_set<std::errc>> &>(),
                             std::declval<const std::expected<
                                 int, bt::error_set<std::errc>> &>())),
        std::expected<int, bt::error_set<std::errc>>>);

} // namespace

TEST_CASE("baseline-capture: golden deductions hold at this commit") {
    // Every assertion in this translation unit is a static_assert, and every
    // one of them is a golden: nothing here is scheduled to change. What was
    // scheduled now lives in current_state.test.cpp.
    SUCCEED("golden deduction matrix compiled");
}
