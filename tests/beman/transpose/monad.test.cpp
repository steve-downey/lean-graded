// tests/beman/transpose/monad.test.cpp                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/monad.hpp>

#include <beman/transpose/functor.hpp>

#include <catch2/catch_test_macros.hpp>

#include <optional>
#include <string>
#include <type_traits>

namespace bt = beman::transpose;

namespace {
template <class M, class F, class MA>
concept has_fmap = requires(M &m, F &f, MA &ma) { m.fmap(f, ma); };
} // namespace

TEST_CASE("monad: optional bind short-circuits on empty") {
    auto half_if_even = [](int x) {
        return x % 2 == 0 ? std::optional<int>{x / 2} : std::optional<int>{};
    };
    REQUIRE(bt::mbind(std::optional<int>{8}, half_if_even) ==
            std::optional<int>{4});
    REQUIRE(bt::mbind(std::optional<int>{7}, half_if_even) ==
            std::optional<int>{});
    REQUIRE(bt::mbind(std::optional<int>{}, half_if_even) ==
            std::optional<int>{});
}

TEST_CASE("monad: join flattens nested optional") {
    std::optional<std::optional<int>> nested{std::optional<int>{5}};
    REQUIRE(bt::join(nested) == std::optional<int>{5});
}

TEST_CASE("monad: invoke synthesized from bind and pure") {
    const auto &m = bt::monad_typeclass<std::optional<int>>;
    auto add3 = [](int a, int b, int c) { return a + b + c; };

    REQUIRE(m.invoke(add3, std::optional<int>{1}, std::optional<int>{2},
                     std::optional<int>{3}) == std::optional<int>{6});
    REQUIRE(m.invoke(add3, std::optional<int>{1}, std::optional<int>{},
                     std::optional<int>{3}) == std::optional<int>{});
}

TEST_CASE("monad: invoke coheres with the applicative invoke") {
    const auto &monad = bt::monad_typeclass<std::optional<int>>;
    const auto &applicative = bt::applicative_typeclass<std::optional<int>>;
    auto add = [](int a, int b) { return a + b; };

    REQUIRE(
        monad.invoke(add, std::optional<int>{4}, std::optional<int>{5}) ==
        applicative.invoke(add, std::optional<int>{4}, std::optional<int>{5}));
    REQUIRE(
        monad.invoke(add, std::optional<int>{}, std::optional<int>{5}) ==
        applicative.invoke(add, std::optional<int>{}, std::optional<int>{5}));
}

TEST_CASE("monad: fmap is the Functor basis grounded in bind + pure") {
    const auto &m = bt::monad_typeclass<std::optional<int>>;
    auto increment = [](int x) { return x + 1; };

    REQUIRE(m.fmap(increment, std::optional<int>{41}) ==
            std::optional<int>{42});
    REQUIRE(m.fmap(increment, std::optional<int>{}) == std::optional<int>{});
}

TEST_CASE("monad: fmap deduces a changed value type") {
    const auto &m = bt::monad_typeclass<std::optional<int>>;
    auto to_string = [](int x) { return std::to_string(x); };

    auto result = m.fmap(to_string, std::optional<int>{7});
    static_assert(std::same_as<decltype(result), std::optional<std::string>>);
    REQUIRE(result == std::optional<std::string>{"7"});
}

TEST_CASE("monad: fmap is not callable with a mismatched function") {
    struct not_invocable_on_int {};
    using not_applicable_t = decltype([](not_invocable_on_int) { return 0; });

    static_assert(!has_fmap<decltype(bt::monad_typeclass<std::optional<int>>),
                            not_applicable_t, std::optional<int>>);
}

namespace {
// An Impl with pure + bind, and a native `join` constrained to
// std::optional<std::optional<int>> only -- a marker the bind derivation
// could never produce, and unreachable for any other element type. This is
// the per-instantiation property `using` could never express: one Impl,
// native for one instantiation, derived for another.
struct PerInstantiationJoinImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class A, class F>
    auto bind(this auto &&, const std::optional<A> &ma, F &&f)
        -> bt::remove_cvref_t<std::invoke_result_t<F, const A &>> {
        using Result = bt::remove_cvref_t<std::invoke_result_t<F, const A &>>;
        if (!ma)
            return Result{};
        return Result{std::invoke(std::forward<F>(f), *ma)};
    }

    auto join(this auto &&, const std::optional<std::optional<int>> &)
        -> std::optional<int> {
        return std::optional<int>{-1};
    }
};

struct PerInstantiationJoinMap : bt::Monad<PerInstantiationJoinImpl> {};

// An Impl with pure + bind, and a native `ap` that ignores both arguments
// and returns a sentinel the bind + pure derivation could never produce.
struct MarkedApImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class A, class F>
    auto bind(this auto &&, const std::optional<A> &ma, F &&f)
        -> bt::remove_cvref_t<std::invoke_result_t<F, const A &>> {
        using Result = bt::remove_cvref_t<std::invoke_result_t<F, const A &>>;
        if (!ma)
            return Result{};
        return Result{std::invoke(std::forward<F>(f), *ma)};
    }

    template <class MF, class MA>
    auto ap(this auto &&, MF &&, MA &&) -> std::optional<int> {
        return std::optional<int>{-1};
    }
};

struct MarkedApMap : bt::Monad<MarkedApImpl> {};
} // namespace

TEST_CASE("monad: join native preference is per instantiation") {
    PerInstantiationJoinMap m{};

    // std::optional<std::optional<int>>: the native join fires.
    REQUIRE(m.join(std::optional<std::optional<int>>{std::optional<int>{5}}) ==
            std::optional<int>{-1});

    // std::optional<std::optional<std::string>>: no native join exists for
    // this element type, so the same member falls back to the bind
    // derivation -- a property a Map-level `using` could never express,
    // since `using` selects a name for every instantiation at once.
    REQUIRE(m.join(std::optional<std::optional<std::string>>{
                std::optional<std::string>{"x"}}) ==
            std::optional<std::string>{"x"});
}

TEST_CASE("monad: ap prefers a native Impl::ap") {
    MarkedApMap m{};
    auto increment = [](int x) { return x + 1; };

    REQUIRE(m.ap(std::optional<decltype(increment)>{increment},
                 std::optional<int>{5}) == std::optional<int>{-1});
}

TEST_CASE("monad: ap falls back to the bind + pure derivation") {
    const auto &m = bt::monad_typeclass<std::optional<int>>;
    auto increment = [](int x) { return x + 1; };

    REQUIRE(m.ap(std::optional<decltype(increment)>{increment},
                 std::optional<int>{5}) == std::optional<int>{6});
}

// ============================================================================
// as-functor-presentation: Monad::as_functor(), the one visible free call
// that names which functor a monad object presents. See
// docs/decisions.md#functor-monad-grounding.
// ============================================================================

TEST_CASE("monad: as_functor is usable in a constant expression and empty") {
    constexpr auto &m = bt::monad_typeclass<std::optional<int>>;
    constexpr auto f = m.as_functor();
    static_assert(std::is_empty_v<decltype(f)>);
    (void)f;
}

namespace {
// The motivating scenario: an algorithm writer holding an opaque monad
// object needing to call a Functor-constrained function. as_functor() is
// what makes the call site sayable.
template <class OBJ>
    requires bt::functor_object<OBJ, std::optional<int>>
auto increment_via_functor_object(const OBJ &f, std::optional<int> value) {
    return f.fmap([](int x) { return x + 1; }, value);
}
} // namespace

TEST_CASE(
    "monad: as_functor lets a functor_object-constrained algorithm accept "
    "an opaque monad object") {
    const auto &m = bt::monad_typeclass<std::optional<int>>;

    REQUIRE(
        increment_via_functor_object(m.as_functor(), std::optional<int>{41}) ==
        std::optional<int>{42});
    REQUIRE(increment_via_functor_object(
                m.as_functor(), std::optional<int>{}) == std::optional<int>{});
}

TEST_CASE("monad: as_functor's fmap computes what the monad's own fmap "
          "computes") {
    const auto &m = bt::monad_typeclass<std::optional<int>>;
    auto f = m.as_functor();
    auto increment = [](int x) { return x + 1; };

    REQUIRE(f.fmap(increment, std::optional<int>{41}) ==
            m.fmap(increment, std::optional<int>{41}));
    REQUIRE(f.fmap(increment, std::optional<int>{}) ==
            m.fmap(increment, std::optional<int>{}));
}

TEST_CASE(
    "monad: as_functor's replace is the fmap-derived answer when the monad "
    "supplies no native replace") {
    const auto &m = bt::monad_typeclass<std::optional<int>>;
    auto f = m.as_functor();

    REQUIRE(f.replace(std::optional<int>{5}, 9) == std::optional<int>{9});
}

namespace {
// An Impl with pure + bind (so Monad grows the Functor basis fmap), whose
// Map additionally supplies its own native `replace` -- distinguishable
// from the fmap derivation by doubling the replacement, the same marker
// shape as functor.test.cpp's MarkedReplaceImpl. as_functor() wraps this Map
// as Functor<ThisMap>, so Functor::replace's native-preference probe lands
// on the Map's own `replace`, not Monad's Impl.
struct NativeReplaceMonadImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class A, class F>
    auto bind(this auto &&, const std::optional<A> &ma, F &&f)
        -> bt::remove_cvref_t<std::invoke_result_t<F, const A &>> {
        using Result = bt::remove_cvref_t<std::invoke_result_t<F, const A &>>;
        if (!ma)
            return Result{};
        return Result{std::invoke(std::forward<F>(f), *ma)};
    }
};

struct NativeReplaceMonadMap : bt::Monad<NativeReplaceMonadImpl> {
    template <class T, class U>
    auto replace(this auto &&, T &&, U &&replacement) -> std::optional<int> {
        return std::optional<int>{replacement + replacement};
    }
};
} // namespace

TEST_CASE("monad: as_functor is optimization-preserving -- a native "
          "Impl::replace wins over the derivation") {
    NativeReplaceMonadMap m{};
    auto f = m.as_functor();

    REQUIRE(f.replace(std::optional<int>{5}, 3) == std::optional<int>{6});
}
