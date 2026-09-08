// tests/beman/transpose/fold.test.cpp                                -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/fold.hpp>

#include "test_support.hpp"

#include <catch2/catch_test_macros.hpp>

#include <functional>
#include <string>
#include <vector>

namespace bt = beman::transpose;

namespace {

template <class M, class F, class T>
concept has_fold_map = requires(M &m, F &f, T &t) { m.fold_map(f, t); };

// An Impl with a native `length` returning a sentinel the fold_map
// derivation could never produce, registered through a Map with no `using`
// for it -- the ergonomics claim, exercised directly: an instance author
// adds a native member and gets it back with no Map edit.
struct MarkerLengthImpl {
    template <class T>
    auto length(this auto &&, const T &) -> std::size_t {
        return 999;
    }
};

struct MarkerLengthMap : bt::Foldable<MarkerLengthImpl> {};

// An Impl with a generic fold_map (any std::vector<V>), and a native
// to_vector constrained to std::vector<int> only -- a marker the fold_map
// derivation could never produce, and unreachable for any other element
// type. This is the per-instantiation property a Map-level `using` could
// never express.
struct PerInstantiationToVectorImpl {
    template <class FUNCTION, class V>
    auto fold_map(this auto &&, FUNCTION &&function,
                  const std::vector<V> &values) {
        using Result =
            bt::remove_cvref_t<std::invoke_result_t<FUNCTION, const V &>>;
        auto accumulated = bt::monoid_identity<Result>();
        for (const auto &value : values) {
            accumulated = bt::monoid_combine(std::move(accumulated),
                                             std::invoke(function, value));
        }
        return accumulated;
    }

    auto to_vector(this auto &&, const std::vector<int> &) -> std::vector<int> {
        return std::vector<int>{-1};
    }
};

struct PerInstantiationToVectorMap
    : bt::Foldable<PerInstantiationToVectorImpl> {};

// The hazard this step closes: an Impl providing only fold_right +
// element_type, no fold_map at all, registered through a Map with no
// using-declaration whatsoever -- the Map body below is exactly its
// definition and nothing else. Before this step, fold_map's derivation and
// fold_right's derivation were both self-routed, so a Map shaped like this
// sent the two into unbounded mutual template recursion (each round nesting
// another RightFoldProgram) rather than a clean answer. After this step,
// fold_map is available and correct because its derivation addresses Impl
// directly instead of re-entering through self.
struct FoldRightOnlyImpl {
    using element_type = int;

    // A plain const member, not an explicit-object one: MSVC's backend
    // ICEs (C1001, p2) emitting the deducing-this form of exactly this
    // body; see the twin in objects.test.cpp.
    template <class STATE, class FUNCTION>
    auto fold_right(const std::vector<int> &values, STATE initial_state,
                    FUNCTION &&function) const -> STATE {
        STATE state = std::move(initial_state);
        for (auto it = values.rbegin(); it != values.rend(); ++it) {
            state = std::invoke(function, *it, std::move(state));
        }
        return state;
    }
};

struct FoldRightOnlyMap : bt::Foldable<FoldRightOnlyImpl> {};

} // namespace

TEST_CASE("fold: length prefers a native Impl::length, no Map using needed") {
    MarkerLengthMap m{};
    REQUIRE(m.length(std::vector<int>{1, 2, 3}) == 999);
}

TEST_CASE("fold: to_vector native preference is per instantiation") {
    PerInstantiationToVectorMap m{};

    // std::vector<int>: the native to_vector fires.
    REQUIRE(m.to_vector(std::vector<int>{1, 2, 3}) == std::vector<int>{-1});

    // std::vector<std::string>: no native to_vector exists for this element
    // type, so the same member falls back to the fold_map derivation.
    REQUIRE(m.to_vector(std::vector<std::string>{"a", "b"}) ==
            std::vector<std::string>{"a", "b"});
}

TEST_CASE("fold: fold_map derives from a fold_right + element_type Impl, "
          "with no Map using-declaration at all") {
    FoldRightOnlyMap m{};
    std::vector<int> xs{1, 2, 3, 4};

    // fold_map itself, via the fold_right basis -- this is the shape that
    // would have recursed unboundedly before this step.
    REQUIRE(m.fold_map([](int) { return bt::Count{1}; }, xs).d_value == 4);

    // The rest of the family, all routed through the same fold_map.
    REQUIRE(m.length(xs) == 4);
    REQUIRE(m.to_vector(xs) == xs);
    REQUIRE(m.fold_right(xs, std::string{}, [](int x, std::string acc) {
        return acc + std::to_string(x);
    }) == "4321");
}

TEST_CASE("fold: fold_map does not exist when Impl provides neither basis") {
    struct NoBasisImpl {};
    struct NoBasisMap : bt::Foldable<NoBasisImpl> {};

    static_assert(!has_fold_map<NoBasisMap, decltype([](int x) { return x; }),
                                std::vector<int>>);
}

TEST_CASE("fold: length and to_vector over Sequence") {
    const auto &f = bt::foldable_typeclass<bt::test::Sequence<int>>;
    bt::test::Sequence<int> seq{{10, 20, 30}};
    REQUIRE(f.length(seq) == 3);
    REQUIRE(f.to_vector(seq) == std::vector<int>{10, 20, 30});
}

TEST_CASE("fold: fold_left and fold_right accumulate") {
    const auto &f = bt::foldable_typeclass<bt::test::Sequence<int>>;
    bt::test::Sequence<int> seq{{1, 2, 3, 4}};
    REQUIRE(f.fold_left(seq, 0, [](int acc, int x) { return acc + x; }) == 10);
    REQUIRE(f.fold_right(seq, std::string{}, [](int x, std::string acc) {
        return acc + std::to_string(x);
    }) == "4321");
}

TEST_CASE("fold: any_of, all_of, find_first") {
    const auto &f = bt::foldable_typeclass<bt::test::Sequence<int>>;
    bt::test::Sequence<int> seq{{2, 4, 6, 7}};
    REQUIRE(f.any_of(seq, [](int x) { return x % 2 == 1; }));
    REQUIRE_FALSE(f.all_of(seq, [](int x) { return x % 2 == 0; }));
    REQUIRE(f.find_first(seq, [](int x) { return x > 5; }) == 6);
}
