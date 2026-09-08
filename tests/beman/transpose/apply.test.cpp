// tests/beman/transpose/apply.test.cpp                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/apply.hpp>
#include <beman/transpose/zip_list.hpp>

#include "test_support.hpp"

#include <catch2/catch_test_macros.hpp>

#include <functional>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace bt = beman::transpose;

namespace {

// An Impl with pure + invoke, and a native map that ignores its arguments
// and returns a sentinel the invoke derivation could never produce.
struct MarkedMapImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function,
                const std::optional<FIRST> &first,
                const std::optional<REST> &...rest)
        -> std::optional<bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>> {
        using Result = bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>;
        if (first.has_value() && (... && rest.has_value())) {
            return std::optional<Result>{
                std::invoke(function, *first, *rest...)};
        }
        return std::optional<Result>{};
    }

    template <class FUNCTION, class ARGUMENT>
    auto map(this auto &&, FUNCTION &&, ARGUMENT &&) -> std::optional<int> {
        return std::optional<int>{-1};
    }
};

struct MarkedMapMap : bt::Applicative<MarkedMapImpl> {};

// Native map is constrained to std::optional<int>, so a different element
// type on the same Map still reaches the invoke derivation.
struct PerInstantiationMapImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function,
                const std::optional<FIRST> &first,
                const std::optional<REST> &...rest)
        -> std::optional<bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>> {
        using Result = bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>;
        if (first.has_value() && (... && rest.has_value())) {
            return std::optional<Result>{
                std::invoke(function, *first, *rest...)};
        }
        return std::optional<Result>{};
    }

    template <class FUNCTION>
    auto map(this auto &&, FUNCTION &&, const std::optional<int> &)
        -> std::optional<int> {
        return std::optional<int>{-1};
    }
};

struct PerInstantiationMapMap : bt::Applicative<PerInstantiationMapImpl> {};

// An Impl with a native zip_with that ignores its arguments and returns a
// sentinel the invoke derivation could never produce.
struct MarkedZipWithImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function,
                const std::optional<FIRST> &first,
                const std::optional<REST> &...rest)
        -> std::optional<bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>> {
        using Result = bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>;
        if (first.has_value() && (... && rest.has_value())) {
            return std::optional<Result>{
                std::invoke(function, *first, *rest...)};
        }
        return std::optional<Result>{};
    }

    template <class FUNCTION, class FIRST_ARGUMENT, class SECOND_ARGUMENT>
    auto zip_with(this auto &&, FUNCTION &&, FIRST_ARGUMENT &&,
                  SECOND_ARGUMENT &&) -> std::optional<int> {
        return std::optional<int>{-1};
    }
};

struct MarkedZipWithMap : bt::Applicative<MarkedZipWithImpl> {};

// An Impl with pure + invoke, and native lift/discard_first/discard_second
// that each return a sentinel their pure/invoke derivations could never
// produce.
struct AllNativeImpl {
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function,
                const std::optional<FIRST> &first,
                const std::optional<REST> &...rest)
        -> std::optional<bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>> {
        using Result = bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>;
        if (first.has_value() && (... && rest.has_value())) {
            return std::optional<Result>{
                std::invoke(function, *first, *rest...)};
        }
        return std::optional<Result>{};
    }

    template <class VALUE>
    auto lift(this auto &&, VALUE &&) -> std::optional<int> {
        return std::optional<int>{-1};
    }

    template <class FIRST_ARGUMENT, class SECOND_ARGUMENT>
    auto discard_first(this auto &&, FIRST_ARGUMENT &&, SECOND_ARGUMENT &&)
        -> std::optional<int> {
        return std::optional<int>{-2};
    }

    template <class FIRST_ARGUMENT, class SECOND_ARGUMENT>
    auto discard_second(this auto &&, FIRST_ARGUMENT &&, SECOND_ARGUMENT &&)
        -> std::optional<int> {
        return std::optional<int>{-3};
    }
};

struct AllNativeMap : bt::Applicative<AllNativeImpl> {};

} // namespace

TEST_CASE("apply: optional invoke combines effectful arguments") {
    const auto &app = bt::applicative_typeclass<std::optional<int>>;
    auto add = [](int a, int b, int c) { return a + b + c; };
    REQUIRE(app.invoke(add, std::optional<int>{1}, std::optional<int>{2},
                       std::optional<int>{3}) == std::optional<int>{6});
    REQUIRE(app.invoke(add, std::optional<int>{1}, std::optional<int>{},
                       std::optional<int>{3}) == std::optional<int>{});
}

TEST_CASE("apply: ap is a supported basis and secondary operation") {
    // invoke is the user-facing interface; ap -- one-step application of a
    // callable-in-context -- is the classic basis, derived here from
    // optional's invoke basis and available as a secondary operation.
    const auto &app = bt::applicative_typeclass<std::optional<int>>;
    auto lifted = app.pure([](int x) { return x * 10; });
    REQUIRE(app.ap(lifted, std::optional<int>{5}) == std::optional<int>{50});
    REQUIRE(app.ap(app.pure([](int x) { return x * 10; }),
                   std::optional<int>{}) == std::optional<int>{});

    // ap agrees with the invoke spelling of the same application.
    auto call = [](const auto &f, int x) { return f(x); };
    REQUIRE(app.ap(lifted, std::optional<int>{5}) ==
            app.invoke(call, lifted, std::optional<int>{5}));

    using Map = bt::remove_cvref_t<decltype(app)>;
    STATIC_REQUIRE(bt::test::has_apply_form<Map, std::optional<int (*)(int)>,
                                            std::optional<int>>);

    // The detail:: free-function form works too.
    REQUIRE(bt::detail::ap(app, lifted, std::optional<int>{5}) ==
            std::optional<int>{50});
}

TEST_CASE("apply: identity and homomorphism laws on optional") {
    using bt::test::check_applicative_homomorphism_law;
    using bt::test::check_applicative_identity_law;
    REQUIRE(check_applicative_identity_law(std::optional<int>{7}));
    REQUIRE(check_applicative_homomorphism_law<std::optional<int>>(
        [](int x) { return x + 1; }, 41));
    // Generalized to the n-ary core: invoke(f, pure(x)...) == pure(f(x...)).
    REQUIRE(check_applicative_homomorphism_law<std::optional<int>>(
        [](int a, int b) { return a + b; }, 20, 22));
    REQUIRE(check_applicative_homomorphism_law<std::optional<int>>(
        [](int a, int b, int c) { return a * b * c; }, 2, 3, 7));
}

TEST_CASE("apply: interchange and composition laws on optional") {
    using bt::test::check_applicative_interchange_law;
    using bt::test::check_functor_composition_law;
    std::optional functions{[](int x) { return x - 5; }};
    REQUIRE(check_applicative_interchange_law(functions, 12));
    REQUIRE(check_functor_composition_law([](int x) { return x * 2; },
                                          [](int x) { return x + 1; },
                                          std::optional<int>{20}));
    REQUIRE(check_functor_composition_law([](int x) { return x * 2; },
                                          [](int x) { return x + 1; },
                                          std::optional<int>{}));
}

TEST_CASE("apply: laws hold for the Identity context") {
    using bt::test::check_applicative_homomorphism_law;
    using bt::test::check_applicative_identity_law;
    using bt::test::check_functor_composition_law;
    using Identity = bt::test::Identity<int>;
    REQUIRE(check_applicative_identity_law(Identity{9}));
    REQUIRE(check_applicative_homomorphism_law<Identity>(
        [](int a, int b) { return a - b; }, 50, 8));
    REQUIRE(check_functor_composition_law(
        [](int x) { return x / 2; }, [](int x) { return x + 6; }, Identity{4}));
}

TEST_CASE("apply: invoke_with delegates to another applicative map") {
    const auto &optional_map = bt::applicative_typeclass<std::optional<int>>;
    const auto &zip_map = bt::applicative_typeclass<bt::zip_list<int>>;
    auto result = optional_map.invoke_with(
        zip_map, [](int a, int b) { return a + b; },
        bt::zip_list<int>{{1, 2, 3}}, bt::zip_list<int>{{10, 20, 30}});
    REQUIRE(result.data == std::vector<int>{11, 22, 33});
}

TEST_CASE("apply: map prefers a native Impl::map") {
    MarkedMapMap m{};
    REQUIRE(m.map([](int x) { return x + 1; }, std::optional<int>{5}) ==
            std::optional<int>{-1});
}

TEST_CASE("apply: map falls back to the invoke derivation") {
    const auto &m = bt::applicative_typeclass<std::optional<int>>;
    REQUIRE(m.map([](int x) { return x + 1; }, std::optional<int>{5}) ==
            std::optional<int>{6});
}

TEST_CASE("apply: map native preference is per instantiation") {
    PerInstantiationMapMap m{};

    // std::optional<int>: the native map fires.
    REQUIRE(m.map([](int x) { return x + 1; }, std::optional<int>{5}) ==
            std::optional<int>{-1});

    // std::optional<std::string>: no native map exists for this element
    // type, so the same member falls back to the invoke derivation -- a
    // property a Map-level `using` could never express, since `using`
    // selects a name for every instantiation at once.
    REQUIRE(m.map([](const std::string &s) { return s + "!"; },
                  std::optional<std::string>{"x"}) ==
            std::optional<std::string>{"x!"});
}

TEST_CASE("apply: zip_with prefers a native Impl::zip_with") {
    MarkedZipWithMap m{};
    REQUIRE(m.zip_with([](int a, int b) { return a + b; },
                       std::optional<int>{2},
                       std::optional<int>{3}) == std::optional<int>{-1});
}

TEST_CASE("apply: zip_with falls back to the invoke derivation") {
    const auto &m = bt::applicative_typeclass<std::optional<int>>;
    REQUIRE(m.zip_with([](int a, int b) { return a + b; },
                       std::optional<int>{2},
                       std::optional<int>{3}) == std::optional<int>{5});
}

TEST_CASE("apply: lift prefers a native Impl::lift") {
    AllNativeMap m{};
    REQUIRE(m.lift(7) == std::optional<int>{-1});
}

TEST_CASE("apply: lift falls back to the pure derivation") {
    const auto &m = bt::applicative_typeclass<std::optional<int>>;
    REQUIRE(m.lift(7) == std::optional<int>{7});
}

TEST_CASE("apply: discard_first prefers a native Impl::discard_first") {
    AllNativeMap m{};
    REQUIRE(m.discard_first(std::optional<int>{2}, std::optional<int>{3}) ==
            std::optional<int>{-2});
}

TEST_CASE("apply: discard_first falls back to the invoke derivation") {
    const auto &m = bt::applicative_typeclass<std::optional<int>>;
    REQUIRE(m.discard_first(std::optional<int>{2}, std::optional<int>{3}) ==
            std::optional<int>{3});
}

TEST_CASE("apply: discard_second prefers a native Impl::discard_second") {
    AllNativeMap m{};
    REQUIRE(m.discard_second(std::optional<int>{2}, std::optional<int>{3}) ==
            std::optional<int>{-3});
}

TEST_CASE("apply: discard_second falls back to the invoke derivation") {
    const auto &m = bt::applicative_typeclass<std::optional<int>>;
    REQUIRE(m.discard_second(std::optional<int>{2}, std::optional<int>{3}) ==
            std::optional<int>{2});
}
