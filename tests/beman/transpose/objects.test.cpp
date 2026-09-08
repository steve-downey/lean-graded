// tests/beman/transpose/objects.test.cpp                             -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <beman/transpose/apply.hpp>
#include <beman/transpose/fold.hpp>
#include <beman/transpose/functor.hpp>
#include <beman/transpose/monad.hpp>
#include <beman/transpose/traverse.hpp>

#include <beman/transpose/array.hpp>
#include <beman/transpose/expected.hpp>
#include <beman/transpose/sender.hpp>
#include <beman/transpose/sequence.hpp>
#include <beman/transpose/simd_lanes.hpp>
#include <beman/transpose/zip_list.hpp>

#include <catch2/catch_test_macros.hpp>

#include <array>
#include <expected>
#include <optional>
#include <string>
#include <utility>
#include <vector>

// This file's assertions cut across five headers (functor.hpp, apply.hpp,
// monad.hpp, fold.hpp, traverse.hpp), so they get their own translation
// unit rather than being scattered across each header's own test file. See
// docs/decisions.md#typeclass-conformance-depth.

namespace bt = beman::transpose;

TEST_CASE("objects: translation unit compiles") {
    // Bootstrap: passes if the file compiles and links. Everything else in
    // this file is a compile-time static_assert.
    REQUIRE(true);
}

namespace {

// -- Applicative-ap-only-probing's fixture, reused, not forked --
//
// tests/beman/transpose/apply.test.cpp already has an ApOnlyImpl/ApOnlyMap
// pair (pure + ap, no invoke) in its own anonymous namespace, added by
// applicative-ap-only-probing as the regression witness for the dual-basis
// derivation. It is a type in an anonymous namespace of a .test.cpp, so
// there is no canonical header to pull it from; this is a second, identical
// copy, local to this translation unit. See
// handoff-to-typeclass-object-concepts.md.
struct ApOnlyImpl {
    template <class VALUE>
    [[maybe_unused]] auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }

    template <class FUNCTION, class ARGUMENT>
    [[maybe_unused]] auto ap(this auto &&,
                             const std::optional<FUNCTION> &function,
                             const std::optional<ARGUMENT> &argument)
        -> std::optional<bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const ARGUMENT &>>> {
        using Result = bt::remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const ARGUMENT &>>;
        if (function.has_value() && argument.has_value()) {
            return std::optional<Result>{std::invoke(*function, *argument)};
        }
        return std::optional<Result>{};
    }
};

struct ApOnlyMap : bt::Applicative<ApOnlyImpl> {};

// -- The shallow gate, made deeper: a hand-rolled object with pure and
// -- nothing else. Structural conformance lets a program hand-implement a
// -- typeclass object without ever touching the CRTP base, so this is not
// -- derived from Applicative<> at all -- it is exactly the object the
// -- library's structural-conformance promise has to reckon with, and the
// -- whole point of this step: this object satisfies the old, shallow
// -- applicative_object_for gate (it has a conforming pure) and must fail
// -- the new, deep applicative_object gate (it has nothing else).
struct PureOnlyApplicativeObject {
    template <class VALUE>
    [[maybe_unused]] auto pure(this auto &&, VALUE &&value)
        -> std::optional<bt::remove_cvref_t<VALUE>> {
        return std::optional<bt::remove_cvref_t<VALUE>>{
            std::forward<VALUE>(value)};
    }
};

// -- foldable_impl's dual-basis fixture: fold_right + element_type, no
// -- fold_map at all. A second, local copy of fold.test.cpp's
// -- FoldRightOnlyImpl -- see the ApOnlyImpl comment above for why this file
// -- keeps its own copy rather than sharing a header.
struct FoldRightOnlyImpl {
    using element_type = int;

    // A plain const member, not an explicit-object one: MSVC's backend
    // ICEs (C1001, p2) emitting the deducing-this form of exactly this
    // body in both TUs that carry it; the Impl contract only needs the
    // call expression to be valid on a const Impl.
    template <class STATE, class FUNCTION>
    [[maybe_unused]] auto fold_right(const std::vector<int> &values,
                                     STATE initial_state,
                                     FUNCTION &&function) const -> STATE {
        STATE state = std::move(initial_state);
        for (auto it = values.rbegin(); it != values.rend(); ++it) {
            state = std::invoke(function, *it, std::move(state));
        }
        return state;
    }
};

// -- A struct supplying no basis at all -- neither pure, fmap, invoke, ap,
// -- bind, fold_map, fold_right, element_type, nor traverse. Plain, not
// -- CRTP-wrapped, so probing it against any *_impl concept is always a
// -- safe name-lookup failure rather than the CRTP-base body-instantiation
// -- hazard docs/decisions.md#typeclass-conformance-depth's rider records.
struct NoBasisImpl {};

} // namespace

// -- Every shipped object satisfies its concept --

static_assert(
    bt::functor_object<bt::OptionalFunctorMap<int>, std::optional<int>>);
static_assert(bt::functor_object<bt::VectorFunctorMap<int>, std::vector<int>>);

static_assert(bt::applicative_object<bt::OptionalApplicativeMap<int>,
                                     std::optional<int>>);
static_assert(bt::applicative_object<
              bt::remove_cvref_t<
                  decltype(bt::applicative_typeclass<bt::zip_list<int>>)>,
              bt::zip_list<int>>);
static_assert(bt::applicative_object<bt::ArrayApplicativeMap<int, 3>,
                                     std::array<int, 3>>);
static_assert(bt::applicative_object<
              bt::remove_cvref_t<
                  decltype(bt::applicative_typeclass<bt::sender<int>>)>,
              bt::sender<int>>);
static_assert(bt::applicative_object<
              bt::remove_cvref_t<decltype(bt::applicative_typeclass<
                                          std::expected<int, std::string>>)>,
              std::expected<int, std::string>>);
static_assert(
    bt::applicative_object<
        bt::remove_cvref_t<decltype(bt::accumulating_applicative_typeclass<
                                    std::expected<int, std::string>>)>,
        std::expected<int, std::string>>);

static_assert(bt::monad_object<bt::OptionalMonadMap<int>, std::optional<int>>);

static_assert(
    bt::foldable_object<bt::VectorFoldableMap<int>, std::vector<int>>);

static_assert(
    bt::traversable_object<bt::VectorTraversableMap<int>, std::vector<int>>);

// -- An ap-only object satisfies applicative_object --
//
// This is the assertion that keeps the dual basis honest at the concept
// level: an object concept written only against invoke-basis instances
// would bake the invoke/ap defect back in, and nothing else in this file
// would catch it.
static_assert(bt::applicative_object<ApOnlyMap, std::optional<int>>);

// -- The simd-shaped object satisfies applicative_object without ap
// -- unconditionally rejecting it --
//
// simd_lanes builds on every machine; the real std::simd::vec instance in
// simd.hpp is gated behind __has_include(<simd>) and simd.test.cpp is not
// built here. simd_lanes's ap happens to work (its storage is plain
// std::array, more permissive than std::simd::vec's hardware register), so
// this assertion exercises the implication's consequent, not its vacuous
// case -- but it is the same implication that would let a context that
// truly cannot hold a callable pass without ap, which an unconditional
// requirement would not.
static_assert(bt::applicative_object<bt::SimdLanesApplicativeMap<int, 4>,
                                     bt::simd_lanes<int, 4>>);

// -- The shallow gate is really deeper now --
//
// applicative_object_for is itself redefined in terms of applicative_object
// (plus the exact-pure-return-type requirement), so it is now at least as
// strong as the deep concept and correctly rejects this object too -- it is
// not a live example of the old shape any more, it is the new shape. What
// this asserts directly is the shape applicative_object_for used to check,
// on its own: a `pure` returning exactly CONTEXT, and nothing else.
static_assert(requires(const PureOnlyApplicativeObject &obj) {
    { obj.pure(std::declval<int>()) } -> std::same_as<std::optional<int>>;
});
static_assert(
    !bt::applicative_object_for<PureOnlyApplicativeObject, std::optional<int>>);
static_assert(
    !bt::applicative_object<PureOnlyApplicativeObject, std::optional<int>>);

// -- A bare monad object fails functor_object --
//
// OptionalMonadMap carries the Functor basis (fmap, grown by Monad per
// docs/decisions.md#functor-monad-grounding) and never the derived surface
// (replace), so it correctly fails functor_object. This is expected, not a
// bug: the remedy is docs/decisions.md#typeclass-conformance-depth's
// forward pointer to as-functor-presentation, which gives Monad a member
// naming the same Functor<> wrapping the next assertion spells by hand.
static_assert(
    !bt::functor_object<bt::OptionalMonadMap<int>, std::optional<int>>);

// -- The layered instance satisfies it --
static_assert(bt::functor_object<bt::Functor<bt::OptionalMonadMap<int>>,
                                 std::optional<int>>);

// -- as_functor() names the same wrapping --
static_assert(
    bt::functor_object<
        bt::remove_cvref_t<
            decltype(bt::monad_typeclass<std::optional<int>>.as_functor())>,
        std::optional<int>>);

// ============================================================================
// typeclass-impl-concepts: the restricted Impl concepts, one per class,
// naming only the minimal complete basis -- the MINIMAL pragma to the deep
// object concepts above. See docs/decisions.md#typeclass-conformance-depth.
// ============================================================================

// -- Every shipped Impl satisfies its concept --

static_assert(
    bt::functor_impl<bt::OptionalFunctorImpl<int>, std::optional<int>>);

static_assert(
    bt::applicative_impl<bt::OptionalApplicativeImpl<int>, std::optional<int>>);
static_assert(
    bt::applicative_impl<bt::ExpectedApplicativeImpl<int, std::string>,
                         std::expected<int, std::string>>);
static_assert(bt::applicative_impl<
              bt::AccumulatingExpectedApplicativeImpl<int, std::string>,
              std::expected<int, std::string>>);
static_assert(
    bt::applicative_impl<bt::ArrayApplicativeImpl<int, 3>, std::array<int, 3>>);
static_assert(
    bt::applicative_impl<bt::ZipListApplicativeImpl<int>, bt::zip_list<int>>);
static_assert(
    bt::applicative_impl<bt::SenderApplicativeImpl<int>, bt::sender<int>>);
static_assert(bt::applicative_impl<bt::SimdLanesApplicativeImpl<int, 4>,
                                   bt::simd_lanes<int, 4>>);

static_assert(bt::monad_impl<bt::OptionalMonadImpl<int>, std::optional<int>>);

static_assert(bt::foldable_impl<bt::VectorFoldableImpl<int>, std::vector<int>>);

static_assert(
    bt::traversable_impl<bt::VectorTraversableImpl<int>, std::vector<int>>);

// -- Both bases of each dual-basis class are accepted --
//
// This is the assertion that keeps the dual basis honest at the Impl-concept
// level, load-bearing beyond this step: an Impl-directed probe can be a
// statement about the wrong object
// (docs/decisions.md#derived-op-native-preference), and applicative_impl and
// foldable_impl are exactly where a concept written only against one basis
// would bake that defect back in.
static_assert(bt::applicative_impl<ApOnlyImpl, std::optional<int>>); // ap-only
static_assert(bt::applicative_impl<bt::OptionalApplicativeImpl<int>,
                                   std::optional<int>>); // invoke-only
static_assert(
    bt::foldable_impl<FoldRightOnlyImpl, std::vector<int>>); // fold_right-only
static_assert(bt::foldable_impl<bt::VectorFoldableImpl<int>,
                                std::vector<int>>); // fold_map-only

// -- The concepts are restricted, not deep --
//
// An Impl supplying only its basis satisfies the Impl concept and fails the
// corresponding object concept. Without this pair, this step would have
// added five names and no invariant.
static_assert(
    bt::functor_impl<bt::OptionalFunctorImpl<int>, std::optional<int>>);
static_assert(
    !bt::functor_object<bt::OptionalFunctorImpl<int>, std::optional<int>>);

static_assert(
    bt::applicative_impl<bt::OptionalApplicativeImpl<int>, std::optional<int>>);
static_assert(!bt::applicative_object<bt::OptionalApplicativeImpl<int>,
                                      std::optional<int>>);

static_assert(bt::monad_impl<bt::OptionalMonadImpl<int>, std::optional<int>>);
static_assert(
    !bt::monad_object<bt::OptionalMonadImpl<int>, std::optional<int>>);

static_assert(bt::foldable_impl<bt::VectorFoldableImpl<int>, std::vector<int>>);
static_assert(
    !bt::foldable_object<bt::VectorFoldableImpl<int>, std::vector<int>>);

static_assert(
    bt::traversable_impl<bt::VectorTraversableImpl<int>, std::vector<int>>);
static_assert(
    !bt::traversable_object<bt::VectorTraversableImpl<int>, std::vector<int>>);

// -- A basis-less Impl fails --
static_assert(!bt::functor_impl<NoBasisImpl, std::optional<int>>);
static_assert(!bt::applicative_impl<NoBasisImpl, std::optional<int>>);
static_assert(!bt::monad_impl<NoBasisImpl, std::optional<int>>);
static_assert(!bt::foldable_impl<NoBasisImpl, std::vector<int>>);
static_assert(!bt::traversable_impl<NoBasisImpl, std::vector<int>>);
