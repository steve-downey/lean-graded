// tests/beman/transpose/detail/typeclass_base.test.cpp               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/detail/typeclass_base.hpp>

#include <catch2/catch_test_macros.hpp>

#include <optional>
#include <type_traits>
#include <vector>

namespace bt = beman::transpose;

TEST_CASE("typeclass_base: applicative_value_t extracts element type") {
    STATIC_REQUIRE(
        std::is_same_v<bt::applicative_value_t<std::optional<int>>, int>);
    STATIC_REQUIRE(
        std::is_same_v<bt::applicative_value_t<std::vector<double>>, double>);
}

namespace {

// Minimal probe standing in for an `Impl`: one stateless operation whose
// result is a constant expression, so the mechanism below can be exercised
// with STATIC_REQUIRE rather than at runtime.
struct Probe {
    constexpr int op(this auto &&) { return 42; }
};

// A CRTP base over `Probe`, carrying the same private `impl_of` shape the
// five real typeclass bases (Functor, Applicative, Monad, Foldable,
// Traversable) carry: `: protected Impl`, plus a private `impl_of` naming
// `bt::impl_ref_t`.
template <class Impl>
struct Inner : protected Impl {
    template <class SELF>
    constexpr auto derived(this SELF &&self) {
        return impl_of(self).op();
    }

  private:
    template <class SELF>
    static constexpr decltype(auto) impl_of(SELF &&self) {
        return static_cast<bt::impl_ref_t<Impl, SELF>>(self);
    }
};

// The registration shape the tree actually uses: a `Map` publicly deriving
// from the CRTP base and adding nothing of its own.
struct InnerMap : Inner<Probe> {};

// A second CRTP base wrapping `InnerMap` -- standing in for
// `Functor<SomeMonadMap>`. `derived` is exposed as Outer's own member,
// forwarding through Outer's own `impl_of`, never as `using
// Impl::derived;`. That is the own-member rule
// (docs/decisions.md#impl-access-through-bases): a `using`-declaration here
// would let `Inner<Probe>::impl_of` see a `self` typed as `Outer<InnerMap>`
// instead of `InnerMap`, and the cast fails with `'Probe' is an inaccessible
// base of 'Outer<InnerMap>'` -- measured in the amendment consult's
// throwaway worktree, not re-derived here.
template <class Impl>
struct Outer : protected Impl {
    template <class SELF>
    constexpr auto derived(this SELF &&self) {
        return impl_of(self).derived();
    }

  private:
    template <class SELF>
    static constexpr decltype(auto) impl_of(SELF &&self) {
        return static_cast<bt::impl_ref_t<Impl, SELF>>(self);
    }
};

using OuterMap = Outer<InnerMap>;

} // namespace

TEST_CASE("typeclass_base: impl_ref_t propagates const") {
    STATIC_REQUIRE(std::is_same_v<bt::impl_ref_t<Probe, const Inner<Probe> &>,
                                  const Probe &>);
    STATIC_REQUIRE(
        std::is_same_v<bt::impl_ref_t<Probe, Inner<Probe> &>, Probe &>);
}

TEST_CASE("typeclass_base: impl_of reaches Impl one level deep") {
    STATIC_REQUIRE(Inner<Probe>{}.derived() == 42);
}

TEST_CASE("typeclass_base: impl_of reaches Impl one level deep through a Map") {
    STATIC_REQUIRE(InnerMap{}.derived() == 42);
}

TEST_CASE("typeclass_base: impl_of reaches Impl two levels deep through a "
          "wrapped Map, via the own-member rule") {
    STATIC_REQUIRE(OuterMap{}.derived() == 42);
}

TEST_CASE("typeclass_base: const propagates end to end through the "
          "two-deep call") {
    constexpr OuterMap const_outer{};
    STATIC_REQUIRE(const_outer.derived() == 42);
}
