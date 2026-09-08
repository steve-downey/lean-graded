// tests/beman/transpose/laws.test.cpp                                -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include "laws.hpp"

#include <beman/transpose/error_set.hpp>
#include <beman/transpose/expected.hpp>
#include <beman/transpose/functor.hpp>
#include <beman/transpose/grade.hpp>
#include <beman/transpose/monad.hpp>

#include <catch2/catch_test_macros.hpp>

#include <expected>
#include <future>
#include <memory>
#include <optional>
#include <system_error>
#include <type_traits>

namespace bt = beman::transpose;
namespace laws = beman::transpose::test::laws;

// =========================================================================
// GRADE PROBES: three distinct named std enum types.
//
// Inside the interim type-ordering fallback's restrictions BY CONSTRUCTION
// -- named, external linkage, stable spelling -- so the harness never
// depends on the P2830 stand-in behaving outside what error_set.hpp
// documents. Three generators give a free semilattice of eight elements,
// which is the smallest sample that exercises every law shape: the unit at
// ∅, idempotence on the diagonal, commutativity off it, and associativity
// on triples that are not all comparable.
// =========================================================================

using empty_grade = bt::error_set<>;
using e_c = bt::error_set<std::errc>;
using e_i = bt::error_set<std::io_errc>;
using e_f = bt::error_set<std::future_errc>;
using e_ci = bt::error_set<std::errc, std::io_errc>;
using e_cf = bt::error_set<std::errc, std::future_errc>;
using e_if = bt::error_set<std::io_errc, std::future_errc>;
using e_cif = bt::error_set<std::errc, std::io_errc, std::future_errc>;

// The eight elements really are eight, not fewer: the interim ordering
// separates the three generators, so no two subsets collapsed into one type.
static_assert(!std::is_same_v<e_c, e_i>);
static_assert(!std::is_same_v<e_c, e_f>);
static_assert(!std::is_same_v<e_i, e_f>);
static_assert(!std::is_same_v<e_ci, e_cf>);
static_assert(!std::is_same_v<e_ci, e_if>);
static_assert(!std::is_same_v<e_cf, e_if>);
static_assert(!std::is_same_v<e_ci, e_cif>);

/** The shipped model, as a harness subject. */
struct error_set_model {
    using grades =
        laws::grade_sample<empty_grade, e_c, e_i, e_f, e_ci, e_cf, e_if, e_cif>;
    using values =
        laws::value_sample<int, std::optional<int>, std::unique_ptr<int>>;
};

static_assert(laws::check_graded_laws<error_set_model>());

// =========================================================================
// THE SECOND MODEL: the Boolean semilattice {⊥, ⊤}.
//
// TEST-ONLY. Where it lives long-term -- here, or shipped as std::optional's
// official grade registration -- is the still-open question
// docs/decisions.md#optional-grade-model, and this stage does not settle it.
// That is why the carrier below is a purpose-built `Fallible`, not
// std::optional: registering std::optional as a graded carrier would answer
// the open question by fiat, and would contradict the ∅-default assertions
// tests/beman/transpose/grade.test.cpp pins on it.
//
// Its job here is to be a LEAK DETECTOR, per
// docs/decisions.md#grade-generality: an abstraction with one model is
// renamed, not generic. Every place this fails to slide in cleanly is a
// framework/model leak and gets logged as a divergence -- never patched
// around, and never smoothed by special-casing the framework to accommodate
// it.
//
// It is also the smallest possible non-trivial grade algebra: two elements,
// no parameters, no type ordering, no canonicalization. Anything the
// framework demands of it is something the framework demands of every
// algebra, which is exactly what makes it diagnostic.
// =========================================================================

namespace beman_transpose_boolean_grade {

/** ⊥: this computation cannot fail. */
struct never_fails {};

/** ⊤: this computation may fail. The whole algebra is {⊥, ⊤} with ⊥ ⊑ ⊤. */
struct may_fail {};

/** The explicit Boolean carrier: a value at a Boolean grade.
 *
 * Deliberately a distinct type rather than std::optional -- see the section
 * comment. `Fallible<T, never_fails>` is the explicit uniform form; framework
 * re-indexing at the model bottom still strips back to bare `T`.
 */
template <class VALUE, class GRADE>
class Fallible {
  public:
    using value_type = VALUE;
    using grade_type = GRADE;

    constexpr Fallible()
        requires std::is_same_v<GRADE, may_fail>
    = default;

    // NOLINTNEXTLINE(*-explicit-constructor) -- promotion is a subsumption
    // coercion and must be implicit, exactly as expected's from-T is.
    constexpr Fallible(VALUE value) : d_value(std::move(value)) {}

    template <class OTHER_GRADE>
        requires bt::grade_subsumes_v<OTHER_GRADE, GRADE>
    constexpr Fallible(const Fallible<VALUE, OTHER_GRADE> &other)
        : d_value(other.d_value) {}

    constexpr auto has_value() const noexcept -> bool {
        return d_value.has_value();
    }

    constexpr auto operator*() const -> const VALUE & { return *d_value; }

    friend auto operator==(const Fallible &, const Fallible &)
        -> bool = default;

  private:
    template <class, class>
    friend class Fallible;

    std::optional<VALUE> d_value;
};

} // namespace beman_transpose_boolean_grade

namespace boolean_grade = beman_transpose_boolean_grade;

using boolean_grade::Fallible;
using boolean_grade::may_fail;
using boolean_grade::never_fails;

namespace beman::transpose {

// -- The algebra: four joins, two bottoms, four order facts. This part is
// -- exactly what a grade algebra should cost, and it slides in cleanly.

template <>
struct grade_join<never_fails, never_fails> {
    using type = never_fails;
};
template <>
struct grade_join<never_fails, may_fail> {
    using type = may_fail;
};
template <>
struct grade_join<may_fail, never_fails> {
    using type = may_fail;
};
template <>
struct grade_join<may_fail, may_fail> {
    using type = may_fail;
};

template <>
struct grade_bottom<never_fails> {
    using type = never_fails;
};
template <>
struct grade_bottom<may_fail> {
    using type = never_fails;
};

template <>
struct grade_subsumes<never_fails, never_fails> : std::true_type {};
template <>
struct grade_subsumes<never_fails, may_fail> : std::true_type {};
template <>
struct grade_subsumes<may_fail, never_fails> : std::false_type {};
template <>
struct grade_subsumes<may_fail, may_fail> : std::true_type {};

struct boolean_grade_model {};

template <>
struct grade_model<never_fails> {
    using type = boolean_grade_model;
};

template <>
struct grade_model<may_fail> {
    using type = boolean_grade_model;
};

template <class CONTEXT>
inline constexpr bool is_fallible_v = false;

template <class VALUE, class GRADE>
inline constexpr bool is_fallible_v<Fallible<VALUE, GRADE>> = true;

template <class VALUE, class GRADE>
struct grade_of<Fallible<VALUE, GRADE>> {
    using type = GRADE;
};

template <class CARRIER>
struct fallible_value_type {
    using type = CARRIER;
};

template <class VALUE, class GRADE>
struct fallible_value_type<Fallible<VALUE, GRADE>> {
    using type = VALUE;
};

template <class CARRIER>
using fallible_value_type_t =
    typename fallible_value_type<remove_cvref_t<CARRIER>>::type;

/** Promotion: a bare value re-indexed at ⊤ acquires the carrier. */
template <class VALUE>
struct rebind_grade<VALUE, may_fail> {
    using type = Fallible<VALUE, may_fail>;
};

/** Re-indexing a carrier at the grade it already has must not nest. */
template <class VALUE, class GRADE>
struct rebind_grade<Fallible<VALUE, GRADE>, may_fail> {
    using type = Fallible<VALUE, may_fail>;
};

/** Re-indexing at the model's own bottom yields the bare value. */
template <class VALUE>
struct rebind_grade<VALUE, never_fails> {
    using type = VALUE;
};

template <class VALUE, class GRADE>
struct rebind_grade<Fallible<VALUE, GRADE>, never_fails> {
    using type = VALUE;
};

template <class CARRIER>
constexpr auto fallible_failed(const CARRIER &carrier) -> bool {
    if constexpr (is_fallible_v<remove_cvref_t<CARRIER>>) {
        return !carrier.has_value();
    } else {
        return false;
    }
}

template <class CARRIER>
constexpr auto fallible_value(const CARRIER &carrier) -> decltype(auto) {
    if constexpr (is_fallible_v<remove_cvref_t<CARRIER>>) {
        return *carrier;
    } else {
        return (carrier);
    }
}

template <class VALUE_TYPE, class GRADE>
struct FallibleApplicativeImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> Fallible<remove_cvref_t<VALUE>, GRADE> {
        return Fallible<remove_cvref_t<VALUE>, GRADE>{
            std::forward<VALUE>(value)};
    }

    template <class FUNCTION, class... CARRIERS>
        requires(sizeof...(CARRIERS) > 0) &&
                (is_fallible_v<remove_cvref_t<CARRIERS>> || ...) &&
                (detail::mixes_with_model<GRADE, CARRIERS> && ...)
    auto invoke(this auto &&, FUNCTION &&function, const CARRIERS &...operands)
        -> detail::mixed_result_t<
            GRADE,
            Fallible<
                remove_cvref_t<std::invoke_result_t<
                    FUNCTION &, const fallible_value_type_t<CARRIERS> &...>>,
                GRADE>,
            CARRIERS...> {
        using Result = remove_cvref_t<std::invoke_result_t<
            FUNCTION &, const fallible_value_type_t<CARRIERS> &...>>;
        using Returned =
            detail::mixed_result_t<GRADE, Fallible<Result, GRADE>, CARRIERS...>;

        if constexpr (std::is_same_v<Returned, Result>) {
            return std::invoke(function, fallible_value(operands)...);
        } else {
            if ((fallible_failed(operands) || ...)) {
                return Returned{};
            }
            return Returned{std::invoke(function, fallible_value(operands)...)};
        }
    }
};

template <class VALUE_TYPE, class GRADE>
struct FallibleApplicativeMap
    : Applicative<FallibleApplicativeImpl<VALUE_TYPE, GRADE>> {
    using FallibleApplicativeImpl<VALUE_TYPE, GRADE>::invoke;
    using FallibleApplicativeImpl<VALUE_TYPE, GRADE>::pure;
};

template <class VALUE_TYPE, class GRADE>
inline constexpr auto applicative_typeclass<Fallible<VALUE_TYPE, GRADE>> =
    FallibleApplicativeMap<VALUE_TYPE, GRADE>{};

} // namespace beman::transpose

/** The Boolean semilattice, as a harness subject. Two elements is the whole
 * algebra, so the sample is exhaustive rather than representative. */
struct boolean_model {
    using grades = laws::grade_sample<never_fails, may_fail>;
    using values =
        laws::value_sample<int, std::optional<int>, std::unique_ptr<int>>;
};

static_assert(laws::check_graded_laws<boolean_model>());

// =========================================================================
// MODEL-DISPATCHED MIXING.
//
// The harness above checks the ALGEBRA and the CARRIER TRAITS, and both
// models pass. This block reaches the place the algebra exists for: a real
// applicative mixing point. The deduced grade must be the framework
// `grade_join_t` of the operands' semantic `grade_of` readings, and a second
// model must drive an actual deduction rather than only passing laws.
// =========================================================================

namespace mixing_point {

constexpr auto add(const int &lhs, const int &rhs) -> int { return lhs + rhs; }

using bare_c = std::expected<int, std::errc>;
using bare_i = std::expected<int, std::io_errc>;
using graded_c = std::expected<int, e_c>;
using graded_i = std::expected<int, e_i>;
using boolean_may = Fallible<int, may_fail>;
using boolean_never = Fallible<int, never_fails>;

using graded_mix = decltype(bt::applicative_typeclass<graded_c>.invoke(
    add, std::declval<const graded_c &>(), std::declval<const graded_i &>()));

static_assert(std::is_same_v<bt::grade_of_t<graded_mix>,
                             bt::grade_join_t<bt::grade_of_t<graded_c>,
                                              bt::grade_of_t<graded_i>>>,
              "The expected mixing point computes the result grade through "
              "grade_join_t.");

static_assert(std::is_same_v<bt::grade_of_t<bare_c>, e_c>);
static_assert(std::is_same_v<bt::grade_of_t<bare_i>, e_i>);

using bare_mix = decltype(bt::applicative_typeclass<bare_c>.invoke(
    add, std::declval<const bare_c &>(), std::declval<const bare_i &>()));

static_assert(std::is_same_v<bare_mix, std::expected<int, e_ci>>);
static_assert(bt::graded_context<bare_mix>);

using framework_prediction = bt::rebind_grade_t<
    int, bt::grade_join_t<bt::grade_of_t<bare_c>, bt::grade_of_t<bare_i>>>;

static_assert(
    std::is_same_v<bare_mix, framework_prediction>,
    "Plain-error expected carriers are semantically graded at singleton "
    "model grades, so grade_of plus grade_join_t predicts the mixed result.");

using boolean_mix = decltype(bt::applicative_typeclass<boolean_may>.invoke(
    add, std::declval<const boolean_may &>(),
    std::declval<const boolean_never &>()));

static_assert(std::is_same_v<boolean_mix, Fallible<int, may_fail>>);
static_assert(
    std::is_same_v<bt::grade_of_t<boolean_mix>,
                   bt::grade_join_t<bt::grade_of_t<boolean_may>,
                                    bt::grade_of_t<boolean_never>>>,
    "The Boolean model drives a real mixed deduction through grade_join_t.");

template <class LEFT, class RIGHT>
concept accepts_boolean_invoke = requires(const LEFT &lhs, const RIGHT &rhs) {
    bt::applicative_typeclass<boolean_may>.invoke(add, lhs, rhs);
};

static_assert(accepts_boolean_invoke<boolean_may, boolean_never>);
static_assert(!accepts_boolean_invoke<boolean_may, graded_c>);

constexpr auto
accepts_expected_value_and_foreign_carrier(const int &expected_value,
                                           const boolean_may &) -> int {
    return expected_value;
}

template <class LEFT, class RIGHT>
concept accepts_expected_invoke = requires(const LEFT &lhs, const RIGHT &rhs) {
    bt::applicative_typeclass<bare_c>.invoke(
        accepts_expected_value_and_foreign_carrier, lhs, rhs);
};

template <class LEFT, class RIGHT>
concept accepts_accumulating_expected_invoke =
    requires(const LEFT &lhs, const RIGHT &rhs) {
        bt::accumulating_applicative_typeclass<bare_c>.invoke(
            accepts_expected_value_and_foreign_carrier, lhs, rhs);
    };

static_assert(accepts_expected_invoke<bare_c, int>);
static_assert(!accepts_expected_invoke<bare_c, boolean_may>);
static_assert(accepts_accumulating_expected_invoke<bare_c, int>);
static_assert(!accepts_accumulating_expected_invoke<bare_c, boolean_may>);

} // namespace mixing_point

// =========================================================================
// FUNCTOR-MONAD GROUNDING: the layered instance, its laws, and the
// agreement between a hand-written Functor and the fmap Monad grows.
//
// std::optional carries both a hand-written functor_typeclass and a Monad
// instance; the latter grows fmap structurally, from bind + pure, and the
// full Functor instance is spelled Functor<OptionalMonadMap<int>>{} rather
// than registered anywhere. This section checks that layered instance
// compiles, satisfies the functor laws, and agrees with the hand-written
// one -- see docs/decisions.md#functor-monad-grounding.
// =========================================================================

namespace functor_monad_grounding {

constexpr bt::Functor<bt::OptionalMonadMap<int>> layered_functor{};

constexpr auto increment(int x) -> int { return x + 1; }
constexpr auto double_it(int x) -> int { return x * 2; }
constexpr auto identity(int x) -> int { return x; }

} // namespace functor_monad_grounding

TEST_CASE("laws: functor identity holds for Functor<OptionalMonadMap>") {
    using namespace functor_monad_grounding;
    REQUIRE(layered_functor.fmap(identity, std::optional<int>{5}) ==
            std::optional<int>{5});
    REQUIRE(layered_functor.fmap(identity, std::optional<int>{}) ==
            std::optional<int>{});
}

TEST_CASE("laws: functor composition holds for Functor<OptionalMonadMap>") {
    using namespace functor_monad_grounding;
    auto composed = [](int x) { return double_it(increment(x)); };

    REQUIRE(
        layered_functor.fmap(composed, std::optional<int>{5}) ==
        layered_functor.fmap(
            double_it, layered_functor.fmap(increment, std::optional<int>{5})));
    REQUIRE(
        layered_functor.fmap(composed, std::optional<int>{}) ==
        layered_functor.fmap(
            double_it, layered_functor.fmap(increment, std::optional<int>{})));
}

TEST_CASE("laws: hand-written Functor and Monad-grown fmap agree on optional") {
    using functor_monad_grounding::increment;

    const auto &functor = bt::functor_typeclass<std::optional<int>>;
    const auto &monad = bt::monad_typeclass<std::optional<int>>;
    auto via_bind = [](std::optional<int> ma) {
        return bt::mbind(
            ma, [](int a) { return std::optional<int>{increment(a)}; });
    };

    for (auto ma : {std::optional<int>{5}, std::optional<int>{}}) {
        REQUIRE(functor.fmap(increment, ma) == monad.fmap(increment, ma));
        REQUIRE(functor.fmap(increment, ma) == via_bind(ma));
    }
}

TEST_CASE("laws: replace reaches fmap through the layered instance") {
    using namespace functor_monad_grounding;
    REQUIRE(layered_functor.replace(std::optional<int>{1}, 9) ==
            std::optional<int>{9});
}

TEST_CASE("laws: the shipped model satisfies the graded laws") {
    // Compile-time only; reaching here means the static_assert above held.
    SUCCEED("error_set is a bounded join-semilattice with coherent carriers");
}

TEST_CASE("laws: a second, unrelated model satisfies the same laws") {
    SUCCEED("the Boolean semilattice passes the harness written against the "
            "concept");
}
