// tests/beman/transpose/probe_harness.test.cpp                       -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

// The Lean model's probe obligations, checked against this implementation.
//
// WHAT THIS FILE IS. steve-downey/lean-graded is a Lean 4 model of this
// library's grading design: `error_set` as the grade, `expected<T,
// error_set<Es...>>` as the carrier, subsumption as implicit conversion, and
// the monad, applicative and traversable operations over them. Every law it
// proves that has a consequence for C++ is exported as one equation, in C++
// vocabulary, to that repository's generated `docs/probe-harness.md`. This
// translation unit is that harness made executable: one TEST_CASE per
// exported equation, named by the Lean theorem it discharges, so a reader
// of either side can find the other by name.
//
// WHAT IT IS NOT. Nothing here is a proof, and nothing here is a
// registration gate. Each equation is checked BY EXAMPLE at std types, with
// fixtures chosen so the cases the proof had to split on are all reached:
// distinct nonempty grades on both sides of a commutativity claim, three
// distinct grades under an associativity claim, zero, one and several
// failures under an accumulating traversal, and a many-to-one renaming
// rather than the identity. That is the discipline the Lean side records
// for its own tests, applied here.
//
// THE VOCABULARY MAP. The harness writes its equations in a small
// C++-flavoured vocabulary that does not quite coincide with this library's
// spelling. `namespace harness` below is that vocabulary, each verb defined
// in terms of exactly one library operation, so that a probe reads like its
// equation and the translation is in one place:
//
//   harness             library
//   pure<G>(a)          std::expected<A, G>{a}
//   transform(x, f)     applicative_typeclass<X>.map(f, x)
//   apply(f, x)         applicative_typeclass<F>.ap(f, x)
//   map2(k, x, y)       applicative_typeclass<X>.invoke(k, x, y)
//   and_then(x, f)      mbind(x, f)
//   widen<G>(x)         grade_subsume<G>(x)
//   flatten(x)          join(x)
//   traverse(f, xs)     traverse(f, xs)            (short-circuit policy)
//   traverse_accumulating(f, xs)
//                       traverse(f, xs, accumulating_applicative_typeclass<C>)
//   transform_error(x, phi)
//                       x.transform_error(phi)     (std::expected's own)
//
// Two of the harness's names have no library operation behind them and are
// findings rather than probes; both are explained at their section:
// `first_error` (the model's projection from accumulated evidence to the
// short-circuiting carrier) and the composed applicative's traversal.
//
// EQUALITY. The harness says "equality is `==` on the carrier after
// conversion": two sides of a law may land at grades that are equal as sets
// but spelled from different operands. Here that is never a conversion at
// all -- canonicalization makes them the same type, and every such probe
// pins that with a static_assert before comparing values. Where one side is
// genuinely narrower (`bind_pure_left`'s `f(x)` against a `bind` that
// joined), `equal_after_widening` performs the one licensed conversion.

#include <beman/transpose/expected.hpp>
#include <beman/transpose/expected.hpp> // re-inclusion / idempotency check

#include <beman/transpose/apply.hpp>
#include <beman/transpose/error_set.hpp>
#include <beman/transpose/grade.hpp>
#include <beman/transpose/monad.hpp>
#include <beman/transpose/sequence.hpp>
#include <beman/transpose/traverse.hpp>

#include <catch2/catch_test_macros.hpp>

#include <concepts>
#include <cstddef>
#include <expected>
#include <functional>
#include <optional>
#include <string>
#include <system_error>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

namespace bt = beman::transpose;

// =========================================================================
// PROBE TYPES. Named, external linkage, stable spelling: the restrictions
// the interim type ordering in error_set.hpp documents. The three source
// kinds are the Lean model's own test fixture (`inductive E | parse | range
// | io`), so a failing probe here and a failing example there name the
// same case. The two target kinds exist for the renaming laws, which the
// Lean side requires to be MANY-TO-ONE: parse and range both collapse to
// format, so a renaming that silently kept them apart would be caught.
// =========================================================================

namespace beman_transpose_lean_probes {

struct err_parse {
    int value{};

    friend auto operator==(const err_parse &, const err_parse &)
        -> bool = default;
};
struct err_range {
    int value{};

    friend auto operator==(const err_range &, const err_range &)
        -> bool = default;
};
struct err_io {
    int value{};

    friend auto operator==(const err_io &, const err_io &) -> bool = default;
};
struct err_format {
    int value{};

    friend auto operator==(const err_format &, const err_format &)
        -> bool = default;
};
struct err_device {
    int value{};

    friend auto operator==(const err_device &, const err_device &)
        -> bool = default;
};

// Defined in probe_harness_cross_tu.cpp with the packs spelled in a
// DIFFERENT order (and, for the second, with a duplicate). If
// canonicalization did not give both spellings one type, these would not
// link: the mangled name of the parameter is the type's identity across
// translation units, and the linker is the comparison.
auto cross_tu_permuted(
    const std::expected<int, bt::error_set<err_io, err_parse, err_range>> &x)
    -> int;
auto cross_tu_deduplicated(
    const std::expected<int, bt::error_set<err_parse, err_range>> &x) -> int;

} // namespace beman_transpose_lean_probes

namespace probes = beman_transpose_lean_probes;

using probes::err_device;
using probes::err_format;
using probes::err_io;
using probes::err_parse;
using probes::err_range;

using set_none = bt::error_set<>;
using set_p = bt::error_set<err_parse>;
using set_r = bt::error_set<err_range>;
using set_i = bt::error_set<err_io>;
using set_pr = bt::error_set<err_parse, err_range>;
using set_pi = bt::error_set<err_parse, err_io>;
using set_ri = bt::error_set<err_range, err_io>;
using set_pri = bt::error_set<err_parse, err_range, err_io>;
using set_f = bt::error_set<err_format>;
using set_fd = bt::error_set<err_format, err_device>;

template <class VALUE, class GRADE>
using at = std::expected<VALUE, GRADE>;

// =========================================================================
// THE HARNESS VOCABULARY. One library operation per verb; see the file
// comment for the table. Every call is qualified so ADL cannot substitute
// a std algorithm of the same name.
// =========================================================================

namespace harness {

template <class GRADE, class VALUE>
auto pure(VALUE value) -> at<VALUE, GRADE> {
    return at<VALUE, GRADE>{std::move(value)};
}

template <class CONTEXT, class FUNCTION>
auto transform(const CONTEXT &context, FUNCTION function) {
    return bt::applicative_typeclass<CONTEXT>.map(function, context);
}

template <class FUNCTIONS, class ARGUMENTS>
auto apply(const FUNCTIONS &functions, const ARGUMENTS &arguments) {
    return bt::applicative_typeclass<FUNCTIONS>.ap(functions, arguments);
}

/** The same application with the operands examined in the other order:
 * the argument's effect first, then the function's. */
template <class FUNCTIONS, class ARGUMENTS>
auto apply_flipped(const FUNCTIONS &functions, const ARGUMENTS &arguments) {
    return bt::applicative_typeclass<FUNCTIONS>.invoke(
        [](const auto &argument, const auto &function) {
            return std::invoke(function, argument);
        },
        arguments, functions);
}

template <class FUNCTIONS, class ARGUMENTS>
auto apply_accumulating(const FUNCTIONS &functions,
                        const ARGUMENTS &arguments) {
    return bt::accumulating_applicative_typeclass<FUNCTIONS>.ap(functions,
                                                                arguments);
}

template <class FUNCTION, class FIRST, class SECOND>
auto map2(FUNCTION function, const FIRST &first, const SECOND &second) {
    return bt::applicative_typeclass<FIRST>.invoke(function, first, second);
}

template <class CONTEXT, class FUNCTION>
auto and_then(const CONTEXT &context, FUNCTION function) {
    return bt::mbind(context, function);
}

template <class GRADE, class CONTEXT>
auto widen(const CONTEXT &context) {
    return bt::grade_subsume<GRADE>(context);
}

template <class NESTED>
auto flatten(const NESTED &nested) {
    return bt::join(nested);
}

template <class FUNCTION, class VALUE>
auto traverse(FUNCTION function, const std::vector<VALUE> &values) {
    return bt::traverse(function, values);
}

template <class FUNCTION, class VALUE>
auto traverse_accumulating(FUNCTION function,
                           const std::vector<VALUE> &values) {
    using Context = std::invoke_result_t<FUNCTION, const VALUE &>;
    return bt::traverse(function, values,
                        bt::accumulating_applicative_typeclass<Context>);
}

template <class CONTEXT, class RENAMING>
auto transform_error(const CONTEXT &context, RENAMING renaming) {
    return context.transform_error(renaming);
}

/** `left == right` after widening `right` to `left`'s grade -- the one
 * conversion the harness licenses. */
template <class LEFT, class RIGHT>
auto equal_after_widening(const LEFT &left, const RIGHT &right) -> bool {
    return left == widen<bt::grade_of_t<LEFT>>(right);
}

// -- The composed applicative (`Comp` in the Lean model) ------------------
// A nested carrier `expected<expected<T, H>, G>` under the componentwise
// applicative: the outer object applies the inner object. Built from the
// library's own two objects and nothing else, so what these probes check is
// that the library's applicative composes, not a third implementation of
// it. Grades stay genuinely nested -- `Comp.ap`'s result is `Comp (g ⊔ g')
// (h ⊔ h')`, never the flattened union -- and that is what `comp_ap`'s
// deduced type carries.

template <class OUTER, class INNER, class VALUE>
auto comp_pure(VALUE value) -> at<at<VALUE, INNER>, OUTER> {
    return at<at<VALUE, INNER>, OUTER>{at<VALUE, INNER>{std::move(value)}};
}

template <class NESTED, class FUNCTION>
auto comp_map(const NESTED &nested, FUNCTION function) {
    return transform(nested, [function](const auto &inner) {
        return transform(inner, function);
    });
}

template <class FUNCTIONS, class ARGUMENTS>
auto comp_ap(const FUNCTIONS &functions, const ARGUMENTS &arguments) {
    return map2(
        [](const auto &inner_functions, const auto &inner_arguments) {
            return apply(inner_functions, inner_arguments);
        },
        functions, arguments);
}

template <class FUNCTION, class FIRST, class SECOND>
auto comp_map2(FUNCTION function, const FIRST &first, const SECOND &second) {
    return map2(
        [function](const auto &inner_first, const auto &inner_second) {
            return map2(function, inner_first, inner_second);
        },
        first, second);
}

/** List traversal under the composed applicative, folded by hand.
 *
 * FINDING, not a probe: this cannot be `bt::traverse(f, xs, comp_policy)`.
 * `traverse` reads the element type of the context it builds off the
 * context TYPE (`applicative_value_t`, which is the carrier's `value_type`),
 * and for a nested `expected` that is the inner carrier, not the value the
 * composed applicative holds. So a composed policy's `pure` cannot satisfy
 * `applicative_object_for`, and the accumulator `traverse` would build is
 * `vector<expected<B, H>>` rather than `vector<B>`. The Lean side's
 * `traverseComp` needs the applicative to say what its value is; this
 * library's policy surface assumes the carrier says it. The equation
 * `traverseComp_eq` is checked below against this fold instead.
 */
template <class OUTER, class INNER, class FUNCTION, class VALUE>
auto traverse_comp(FUNCTION function, const std::vector<VALUE> &values) {
    using Nested = std::invoke_result_t<FUNCTION, const VALUE &>;
    using Element = typename Nested::value_type::value_type;
    auto accumulated = comp_pure<OUTER, INNER>(std::vector<Element>{});
    for (const auto &value : values) {
        accumulated = comp_map2(
            [](std::vector<Element> collected, const Element &element) {
                collected.push_back(element);
                return collected;
            },
            accumulated, std::invoke(function, value));
    }
    return accumulated;
}

} // namespace harness

// =========================================================================
// FIXTURES.
// =========================================================================

namespace {

auto fail_p(int payload) -> at<int, set_p> {
    return at<int, set_p>{std::unexpect, err_parse{payload}};
}
auto fail_r(int payload) -> at<int, set_r> {
    return at<int, set_r>{std::unexpect, err_range{payload}};
}
auto fail_i(int payload) -> at<int, set_i> {
    return at<int, set_i>{std::unexpect, err_io{payload}};
}

/** Negative inputs fail with parse, inputs over 100 fail with range;
 * everything else doubles. Graded at the union of what it may raise. */
auto classify(int x) -> at<int, set_pr> {
    if (x < 0) {
        return at<int, set_pr>{std::unexpect, err_parse{x}};
    }
    if (x > 100) {
        return at<int, set_pr>{std::unexpect, err_range{x}};
    }
    return at<int, set_pr>{x * 2};
}

/** The many-to-one renaming the morphism laws quantify over: parse and
 * range both become format (distinguishably, so which one arrived is
 * still visible), io becomes device. */
struct collapse {
    auto operator()(const err_parse &e) const -> err_format {
        return err_format{e.value};
    }
    auto operator()(const err_range &e) const -> err_format {
        return err_format{e.value + 1000};
    }
    auto operator()(const err_io &e) const -> err_device {
        return err_device{e.value};
    }
};

/** Lifts a renaming of error KINDS to a function on the witnessed error
 * set, landing in TARGET -- the harness's `phi` as `transform_error` needs
 * it. The short-circuiting carrier always holds exactly one witness, which
 * is what `visit` requires. */
template <class TARGET>
auto renaming(collapse phi) {
    return [phi](const auto &witnessed) -> TARGET {
        return witnessed.visit(
            [&phi](const auto &error) -> TARGET { return TARGET(phi(error)); });
    };
}

auto increment(int x) -> int { return x + 1; }
auto twice(int x) -> int { return x * 2; }

using increment_fn = int (*)(int);

auto to_text(int x) -> at<std::string, set_r> {
    if (x > 100) {
        return at<std::string, set_r>{std::unexpect, err_range{x}};
    }
    return at<std::string, set_r>{std::to_string(x)};
}

auto length_checked(const std::string &s) -> at<std::size_t, set_i> {
    if (s.size() > 2) {
        return at<std::size_t, set_i>{std::unexpect,
                                      err_io{static_cast<int>(s.size())}};
    }
    return at<std::size_t, set_i>{s.size()};
}

} // namespace

TEST_CASE("probe-harness: bootstrap") {
    // Passes if the file compiles, links -- which for this file means the
    // cross-TU identity below held -- and Catch2 is wired up.
    REQUIRE(true);
}

// =========================================================================
// Graded/GradeFold.lean -- canonicalization as type identity.
//
// The Lean side proves `joinAll_perm` and `joinAll_dedup` about a sorted
// normal form, and stops there: it owns the normal-form mathematics, this
// side owns type identity. The two static_asserts are that boundary, and
// the two link-time checks are what a static_assert cannot see -- that a
// second translation unit agrees.
// =========================================================================

// joinAll_perm: error_set<Es...> == error_set<permutation of Es...>
static_assert(std::same_as<bt::error_set<err_parse, err_range, err_io>,
                           bt::error_set<err_io, err_parse, err_range>>);
static_assert(std::same_as<bt::error_set<err_range, err_parse>, set_pr>);

// joinAll_dedup: error_set<Es..., duplicates removed> == error_set<Es...>
static_assert(
    std::same_as<bt::error_set<err_parse, err_parse, err_range>, set_pr>);
static_assert(std::same_as<bt::error_set<err_io, err_io>, set_i>);

// The join IS pack concatenation under the alias, which is what makes the
// two facts above the whole of grade arithmetic.
static_assert(std::same_as<bt::grade_join_t<set_p, set_r>, set_pr>);
static_assert(std::same_as<bt::grade_join_t<set_pr, set_r>, set_pr>);
static_assert(std::same_as<bt::grade_join_t<set_none, set_p>, set_p>);
static_assert(std::same_as<bt::grade_join_t<set_r, set_p>,
                           bt::grade_join_t<set_p, set_r>>);

// rename_cast: "transform_error commutes with a same-set grade cast". In
// C++ a same-set cast is not an operation: the two spellings are one type,
// so the cast the Lean statement carries has no residue here. The
// static_asserts above are the whole of it.

TEST_CASE("probe-harness: GradeFold.joinAll_perm across translation units") {
    // The declaration in this TU spells the pack <io, parse, range>; the
    // definition spells it <parse, range, io>. Linking succeeded, so the
    // mangled names agree, so the types are one.
    const at<int, set_pri> x{7};
    REQUIRE(probes::cross_tu_permuted(x) == 7);
}

TEST_CASE("probe-harness: GradeFold.joinAll_dedup across translation units") {
    // Definition spelled <parse, range, parse>.
    const at<int, set_pr> x{9};
    REQUIRE(probes::cross_tu_deduplicated(x) == 9);
}

// =========================================================================
// Graded/Monad.lean -- and_then at the union grade.
//
// Every continuation here returns a DIFFERENT error set from its input, so
// each probe exercises the graded core of ExpectedMonadImpl (the mixing
// point), and the result grade is a join the Lean statement had to cast
// across. The static_asserts are those casts, discharged by type identity.
// =========================================================================

TEST_CASE("probe-harness: Monad.bind_pure_left") {
    // and_then(pure(x), f) == f(x)
    auto left = harness::and_then(harness::pure<set_p>(42), to_text);
    static_assert(std::same_as<decltype(left), at<std::string, set_pr>>);
    REQUIRE(harness::equal_after_widening(left, to_text(42)));

    auto left_failing = harness::and_then(harness::pure<set_p>(500), to_text);
    REQUIRE(harness::equal_after_widening(left_failing, to_text(500)));
    REQUIRE(left_failing.error().holds<err_range>());
}

TEST_CASE("probe-harness: Monad.bind_pure_right") {
    // and_then(x, pure) == x -- with pure at a different grade than x, so
    // the join is real and the equation is up to widening.
    auto pure_r = [](int a) { return harness::pure<set_r>(a); };

    auto ok = harness::and_then(harness::pure<set_p>(3), pure_r);
    static_assert(std::same_as<decltype(ok), at<int, set_pr>>);
    REQUIRE(harness::equal_after_widening(ok, harness::pure<set_p>(3)));

    auto failing = harness::and_then(fail_p(-1), pure_r);
    REQUIRE(harness::equal_after_widening(failing, fail_p(-1)));
}

TEST_CASE("probe-harness: Monad.bind_assoc") {
    // and_then(and_then(x, f), k) ==
    //     and_then(x, [=](auto a){ return and_then(f(a), k); })
    // Three distinct nonempty grades: x at {parse}, f into {range}, k into
    // {io}. The left side joins as (p ⊔ r) ⊔ i and the right as p ⊔ (r ⊔
    // i); that they are one type is `join_assoc` paid by canonicalization.
    auto rhs_continuation = [](int a) {
        return harness::and_then(to_text(a), length_checked);
    };
    auto check = [&](const at<int, set_p> &x) {
        auto left =
            harness::and_then(harness::and_then(x, to_text), length_checked);
        auto right = harness::and_then(x, rhs_continuation);
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(std::same_as<decltype(left), at<std::size_t, set_pri>>);
        REQUIRE(left == right);
        return left;
    };

    REQUIRE(*check(at<int, set_p>{42}) == 2);
    REQUIRE(check(fail_p(-1)).error().holds<err_parse>());
    REQUIRE(check(at<int, set_p>{500}).error().holds<err_range>());
    REQUIRE(
        check(at<int, set_p>{100}).error().holds<err_io>()); // "100" is long
}

TEST_CASE("probe-harness: Monad.bind_map") {
    // and_then(x, [=](auto a){ return pure(f(a)); }) == transform(x, f)
    auto pure_of_f = [](int a) { return harness::pure<set_pr>(twice(a)); };

    auto x = classify(21);
    REQUIRE(harness::and_then(x, pure_of_f) == harness::transform(x, twice));

    auto failing = classify(-1);
    REQUIRE(harness::and_then(failing, pure_of_f) ==
            harness::transform(failing, twice));
}

TEST_CASE("probe-harness: Monad.bind_widen") {
    // and_then(widen<Es2>(x), f) == widen<Es2 | Fs>(and_then(x, f))
    // x at {parse}, widened to {parse, io}; f into {range}.
    auto check = [](const at<int, set_p> &x) {
        auto left = harness::and_then(harness::widen<set_pi>(x), to_text);
        auto right = harness::widen<set_pri>(harness::and_then(x, to_text));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
        return left;
    };

    REQUIRE(*check(at<int, set_p>{7}) == "7");
    REQUIRE(check(fail_p(-1)).error().holds<err_parse>());
    REQUIRE(check(at<int, set_p>{500}).error().holds<err_range>());
}

// =========================================================================
// Graded/Applicative.lean -- apply, derived from the monad.
//
// `apply` is one-step application, the library's `ap`, which it recovers
// from the n-ary `invoke`. The function operand and the argument operand
// sit at distinct nonempty grades throughout, so every apply is a mixing
// point.
// =========================================================================

TEST_CASE("probe-harness: Applicative.ap_pure_id") {
    // apply(pure(id), x) == x
    auto id = [](int a) { return a; };
    auto pure_id = harness::pure<set_p>(id);

    auto x = fail_r(-3);
    auto applied = harness::apply(pure_id, x);
    static_assert(std::same_as<decltype(applied), at<int, set_pr>>);
    REQUIRE(harness::equal_after_widening(applied, x));
    REQUIRE(harness::equal_after_widening(
        harness::apply(pure_id, harness::pure<set_r>(5)),
        harness::pure<set_r>(5)));
}

TEST_CASE("probe-harness: Applicative.ap_pure_pure") {
    // apply(pure(f), pure(a)) == pure(f(a))
    auto applied = harness::apply(harness::pure<set_p>(increment),
                                  harness::pure<set_r>(41));
    static_assert(std::same_as<decltype(applied), at<int, set_pr>>);
    REQUIRE(applied == harness::pure<set_pr>(42));
}

TEST_CASE("probe-harness: Applicative.ap_interchange") {
    // apply(u, pure(a)) == apply(pure([=](auto f){ return f(a); }), u)
    auto evaluate_at_41 = [](increment_fn f) { return f(41); };

    at<increment_fn, set_p> u{increment};
    auto left = harness::apply(u, harness::pure<set_r>(41));
    auto right = harness::apply(harness::pure<set_r>(evaluate_at_41), u);
    // Both sides are the join of {parse} and {range}, spelled from
    // opposite operand orders: `join_comm` as type identity.
    static_assert(std::same_as<decltype(left), decltype(right)>);
    REQUIRE(left == right);
    REQUIRE(*left == 42);

    at<increment_fn, set_p> u_failing{std::unexpect, err_parse{-1}};
    REQUIRE(harness::apply(u_failing, harness::pure<set_r>(41)) ==
            harness::apply(harness::pure<set_r>(evaluate_at_41), u_failing));
}

TEST_CASE("probe-harness: Applicative.ap_comp") {
    // apply(apply(apply(pure(compose), u), v), w) == apply(u, apply(v, w))
    // u at {parse}, v at {range}, w at {io}: three distinct grades, so
    // the left side's join is bracketed ((p ⊔ r) ⊔ i) and the right's
    // (p ⊔ (r ⊔ i)).
    auto compose = [](increment_fn f) {
        return
            [f](increment_fn g) { return [f, g](int x) { return f(g(x)); }; };
    };
    using u_type = at<increment_fn, set_p>;
    using v_type = at<increment_fn, set_r>;
    using w_type = at<int, set_i>;

    auto check = [&](const u_type &u, const v_type &v, const w_type &w) {
        auto left = harness::apply(
            harness::apply(harness::apply(harness::pure<set_p>(compose), u), v),
            w);
        auto right = harness::apply(u, harness::apply(v, w));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(std::same_as<decltype(left), at<int, set_pri>>);
        REQUIRE(left == right);
        return left;
    };

    REQUIRE(*check(u_type{increment}, v_type{twice}, w_type{20}) == 41);
    REQUIRE(
        check(u_type{std::unexpect, err_parse{1}}, v_type{twice}, w_type{20})
            .error()
            .holds<err_parse>());
    REQUIRE(check(u_type{increment}, v_type{std::unexpect, err_range{2}},
                  w_type{20})
                .error()
                .holds<err_range>());
    REQUIRE(check(u_type{increment}, v_type{twice},
                  w_type{std::unexpect, err_io{3}})
                .error()
                .holds<err_io>());
    // Two failures: both sides keep the LEFTMOST, which is u's on both
    // bracketings -- the law holds without a side condition even though
    // the short-circuiting object drops v's error.
    REQUIRE(check(u_type{std::unexpect, err_parse{1}},
                  v_type{std::unexpect, err_range{2}}, w_type{20})
                .error()
                .witness<err_parse>() == std::optional{err_parse{1}});
}

TEST_CASE("probe-harness: Applicative.ap_flip") {
    // apply(f, x) == apply_flipped(f, x)  // only when at most one side errs
    at<increment_fn, set_p> f_ok{increment};
    at<increment_fn, set_p> f_bad{std::unexpect, err_parse{1}};
    auto x_ok = harness::pure<set_r>(1);
    auto x_bad = fail_r(2);

    auto left = harness::apply(f_ok, x_ok);
    auto right = harness::apply_flipped(f_ok, x_ok);
    static_assert(std::same_as<decltype(left), decltype(right)>);
    REQUIRE(left == right);
    REQUIRE(harness::apply(f_bad, x_ok) == harness::apply_flipped(f_bad, x_ok));
    REQUIRE(harness::apply(f_ok, x_bad) == harness::apply_flipped(f_ok, x_bad));

    // The side condition is necessary: when both err, the two orders keep
    // different errors. This is the counterexample the Lean statement
    // excludes, present here so the exclusion is seen to be load-bearing.
    auto both_left = harness::apply(f_bad, x_bad);
    auto both_right = harness::apply_flipped(f_bad, x_bad);
    REQUIRE(both_left != both_right);
    REQUIRE(both_left.error().holds<err_parse>());
    REQUIRE(both_right.error().holds<err_range>());
}

// =========================================================================
// Graded/Accum.lean -- the same four laws for the accumulating object.
//
// Same carrier, same grades, different object: every failing operand's
// witness survives. The equations are the same text; the difference shows
// in the both-fail cases, where the accumulated evidence on the two sides
// must agree as a witnessed set.
// =========================================================================

TEST_CASE("probe-harness: Accum.ap_pure_id") {
    auto id = [](int a) { return a; };
    auto pure_id = harness::pure<set_p>(id);
    REQUIRE(harness::equal_after_widening(
        harness::apply_accumulating(pure_id, fail_r(-3)), fail_r(-3)));
    REQUIRE(harness::equal_after_widening(
        harness::apply_accumulating(pure_id, harness::pure<set_r>(5)),
        harness::pure<set_r>(5)));
}

TEST_CASE("probe-harness: Accum.ap_pure_pure") {
    REQUIRE(harness::apply_accumulating(harness::pure<set_p>(increment),
                                        harness::pure<set_r>(41)) ==
            harness::pure<set_pr>(42));
}

TEST_CASE("probe-harness: Accum.ap_interchange") {
    auto evaluate_at_41 = [](increment_fn f) { return f(41); };
    at<increment_fn, set_p> u{std::unexpect, err_parse{-1}};
    auto left = harness::apply_accumulating(u, harness::pure<set_r>(41));
    auto right =
        harness::apply_accumulating(harness::pure<set_r>(evaluate_at_41), u);
    static_assert(std::same_as<decltype(left), decltype(right)>);
    REQUIRE(left == right);
}

TEST_CASE("probe-harness: Accum.ap_comp") {
    auto compose = [](increment_fn f) {
        return
            [f](increment_fn g) { return [f, g](int x) { return f(g(x)); }; };
    };
    using u_type = at<increment_fn, set_p>;
    using v_type = at<increment_fn, set_r>;
    using w_type = at<int, set_i>;

    auto check = [&](const u_type &u, const v_type &v, const w_type &w) {
        auto left = harness::apply_accumulating(
            harness::apply_accumulating(
                harness::apply_accumulating(harness::pure<set_p>(compose), u),
                v),
            w);
        auto right =
            harness::apply_accumulating(u, harness::apply_accumulating(v, w));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(std::same_as<decltype(left), at<int, set_pri>>);
        REQUIRE(left == right);
        return left;
    };

    REQUIRE(*check(u_type{increment}, v_type{twice}, w_type{20}) == 41);

    // All three fail: the accumulated evidence is the same witnessed set
    // on both bracketings. This is where `Accum.ap_comp` cites
    // associativity of the evidence monoid, and where the short-circuit
    // probe above only ever saw u's error.
    auto all_failing = check(u_type{std::unexpect, err_parse{1}},
                             v_type{std::unexpect, err_range{2}},
                             w_type{std::unexpect, err_io{3}});
    REQUIRE(all_failing.error().witness_count() == 3);
    REQUIRE(all_failing.error().witness<err_parse>() ==
            std::optional{err_parse{1}});
    REQUIRE(all_failing.error().witness<err_range>() ==
            std::optional{err_range{2}});
    REQUIRE(all_failing.error().witness<err_io>() == std::optional{err_io{3}});
}

// =========================================================================
// Graded/AccumKinds.lean -- accumulation against short-circuiting, per
// kind.
//
// The model's accumulating carrier holds a LIST of errors in source order
// and projects to the short-circuiting carrier by its head. This object
// stores one witness PER KIND, left-biased, in canonical type order
// (docs/decisions.md#accumulation-evidence), so which kind failed first is
// not recorded and no projection from the accumulated value recovers the
// short-circuit result -- `Kinds.noFirstError` proves that in the model.
// What the model states about the carrier this library actually has is
// the per-kind set `Accum.Kinds`, and the four cases below are named for
// its theorems: which kinds a traversal's evidence holds, that widening
// preserves them, that an application's evidence is the union, and what
// the short-circuiting result says about the set. The list-form theorems
// (`toGraded_traverseK`, `errsOf_traverseK`, ...) carry no C++ equation.
// =========================================================================

TEST_CASE("probe-harness: AccumKinds.Kinds.mem_kindsOf_traverseK") {
    // A kind is present exactly when some position raised it; a kind
    // raised twice is present once. The witness kept is the LEFTMOST of
    // that kind -- the payload clause the tag-only model cannot state, and
    // checked here anyway. Fixture: zero, one and several failures, and a
    // repeated kind so left-bias is visible.
    auto zero =
        harness::traverse_accumulating(classify, std::vector<int>{1, 2, 3});
    REQUIRE(zero.has_value());

    auto one =
        harness::traverse_accumulating(classify, std::vector<int>{1, -7, 3});
    REQUIRE_FALSE(one.has_value());
    REQUIRE(one.error().witness_count() == 1);
    REQUIRE(one.error().witness<err_parse>() == std::optional{err_parse{-7}});

    auto several = harness::traverse_accumulating(
        classify, std::vector<int>{1, -7, 300, -8, 400});
    REQUIRE_FALSE(several.has_value());
    REQUIRE(several.error().witness_count() == 2);
    REQUIRE(several.error().witness<err_parse>() ==
            std::optional{err_parse{-7}});
    REQUIRE(several.error().witness<err_range>() ==
            std::optional{err_range{300}});
}

TEST_CASE("probe-harness: AccumTraverse.traverseK_ok") {
    // traverse(f, xs) == pure(transform(xs, f)) when every check succeeds
    const std::vector<int> xs{1, 2, 3};
    auto result = harness::traverse_accumulating(classify, xs);
    REQUIRE(result == harness::pure<set_pr>(std::vector<int>{2, 4, 6}));
    // And it is the short-circuiting result, which is the traverseK_ok
    // half of toGraded_traverseK.
    REQUIRE(result == harness::traverse(classify, xs));
}

TEST_CASE("probe-harness: AccumKinds.Kinds.kindsOf_widen") {
    // Widening moves the membership proof and not the evidence: every
    // kind present before is present after, none is added. Both objects
    // share one carrier here, so the conversion is the same conversion,
    // and the probe is that it loses nothing.
    auto accumulated =
        harness::traverse_accumulating(classify, std::vector<int>{-1, 200});
    auto widened = harness::widen<set_pri>(accumulated);
    static_assert(
        std::same_as<decltype(widened), at<std::vector<int>, set_pri>>);
    REQUIRE(widened.error().witness_count() == 2);
    REQUIRE(widened.error().witness<err_parse>() ==
            accumulated.error().witness<err_parse>());
    REQUIRE(widened.error().witness<err_range>() ==
            accumulated.error().witness<err_range>());
    REQUIRE_FALSE(widened.error().holds<err_io>());

    auto single =
        harness::traverse_accumulating(classify, std::vector<int>{1, 200});
    REQUIRE(harness::widen<set_pri>(single) ==
            harness::widen<set_pri>(
                harness::traverse(classify, std::vector<int>{1, 200})));
}

TEST_CASE("probe-harness: AccumKinds.Kinds.kindsOf_apK") {
    // The evidence of an application is the union of the evidence, and
    // the short-circuit result's kind carries the same witness in it
    // (Kinds.toGraded_mem); with one failing side the two results are
    // equal outright (Kinds.toGraded_of_kindsOf_singleton).
    at<increment_fn, set_p> f_ok{increment};
    at<increment_fn, set_p> f_bad{std::unexpect, err_parse{1}};
    auto x_ok = harness::pure<set_r>(41);
    auto x_bad = fail_r(2);

    REQUIRE(harness::apply_accumulating(f_ok, x_ok) ==
            harness::apply(f_ok, x_ok));
    REQUIRE(harness::apply_accumulating(f_bad, x_ok) ==
            harness::apply(f_bad, x_ok));
    REQUIRE(harness::apply_accumulating(f_ok, x_bad) ==
            harness::apply(f_ok, x_bad));

    auto accumulated = harness::apply_accumulating(f_bad, x_bad);
    auto short_circuited = harness::apply(f_bad, x_bad);
    static_assert(
        std::same_as<decltype(accumulated), decltype(short_circuited)>);
    REQUIRE(short_circuited.error().holds<err_parse>());
    REQUIRE(accumulated.error().witness<err_parse>() ==
            short_circuited.error().witness<err_parse>());
    REQUIRE(accumulated.error().witness_count() == 2);
}

TEST_CASE("probe-harness: AccumKinds.Kinds.toGraded_mem") {
    // Whatever kind the short-circuiting traversal stopped on, the
    // accumulating one holds that kind with the same witness; with exactly
    // one failing position the two results are equal outright
    // (Kinds.toGraded_of_kindsOf_singleton). Zero, one and several
    // failures.
    const std::vector<int> none{1, 2, 3};
    REQUIRE(harness::traverse_accumulating(classify, none) ==
            harness::traverse(classify, none));

    const std::vector<int> one{1, 300, 3};
    REQUIRE(harness::traverse_accumulating(classify, one) ==
            harness::traverse(classify, one));

    const std::vector<int> several{1, 300, -7, 400};
    auto accumulated = harness::traverse_accumulating(classify, several);
    auto short_circuited = harness::traverse(classify, several);
    static_assert(
        std::same_as<decltype(accumulated), decltype(short_circuited)>);
    REQUIRE(short_circuited.error().witness<err_range>() ==
            std::optional{err_range{300}});
    REQUIRE(accumulated.error().witness<err_range>() ==
            short_circuited.error().witness<err_range>());
    REQUIRE(accumulated.error().witness<err_parse>() ==
            std::optional{err_parse{-7}});
}

// =========================================================================
// Graded/Morphism.lean and Graded/Sufficient/MorphismK.lean -- renaming.
//
// A grade morphism is a function on error kinds; here it is lifted to the
// witnessed set and applied through std::expected's own `transform_error`.
// The renaming is many-to-one (parse and range both to format), so a law
// that held only for injective renamings would fail here.
// =========================================================================

TEST_CASE("probe-harness: Morphism.rename_map") {
    // transform_error(transform(x, f), phi) == transform(transform_error(x,
    // phi), f)
    auto phi = renaming<set_f>(collapse{});
    for (int input : {21, -1, 300}) {
        auto x = classify(input);
        auto left = harness::transform_error(harness::transform(x, twice), phi);
        auto right =
            harness::transform(harness::transform_error(x, phi), twice);
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: Morphism.rename_widen") {
    // transform_error(widen<Es2>(x), phi) ==
    //     widen<image of Es2>(transform_error(x, phi))
    // x at {parse}, widened to {parse, io}; the image of {parse, io} under
    // collapse is {format, device}, of {parse} alone is {format}.
    for (const auto &x : {harness::pure<set_p>(1), fail_p(-1)}) {
        auto left = harness::transform_error(harness::widen<set_pi>(x),
                                             renaming<set_fd>(collapse{}));
        auto right = harness::widen<set_fd>(
            harness::transform_error(x, renaming<set_f>(collapse{})));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: Morphism.rename_pure") {
    // transform_error(pure(a), phi) == pure(a)
    REQUIRE(harness::transform_error(harness::pure<set_pr>(5),
                                     renaming<set_f>(collapse{})) ==
            harness::pure<set_f>(5));
}

TEST_CASE("probe-harness: MorphismK.GradedHom.hom_ok") {
    // transform_error(ok(a), phi) == ok(a) at EVERY error set, not only
    // the empty one where the pure law states it: here at the full
    // three-kind set, with a renaming that is not injective.
    REQUIRE(harness::transform_error(harness::pure<set_pri>(5),
                                     renaming<set_fd>(collapse{})) ==
            harness::pure<set_fd>(5));
    REQUIRE(harness::transform_error(harness::pure<set_i>(5),
                                     renaming<set_fd>(collapse{})) ==
            harness::pure<set_fd>(5));
}

TEST_CASE("probe-harness: Morphism.rename_bind") {
    // transform_error(and_then(x, f), phi) ==
    //     and_then(transform_error(x, phi), transform_error(_, phi) compose f)
    auto phi = renaming<set_f>(collapse{});
    auto renamed_to_text = [phi](int a) {
        return harness::transform_error(to_text(a), phi);
    };
    for (const auto &x :
         {harness::pure<set_p>(7), harness::pure<set_p>(500), fail_p(-1)}) {
        auto left =
            harness::transform_error(harness::and_then(x, to_text), phi);
        auto right = harness::and_then(harness::transform_error(x, phi),
                                       renamed_to_text);
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: Morphism.rename_ap") {
    // transform_error(apply(f, x), phi) ==
    //     apply(transform_error(f, phi), transform_error(x, phi))
    auto phi = renaming<set_f>(collapse{});
    at<increment_fn, set_p> f_ok{increment};
    at<increment_fn, set_p> f_bad{std::unexpect, err_parse{1}};
    for (const auto &f : {f_ok, f_bad}) {
        for (const auto &x : {harness::pure<set_r>(41), fail_r(2)}) {
            auto left = harness::transform_error(harness::apply(f, x), phi);
            auto right = harness::apply(harness::transform_error(f, phi),
                                        harness::transform_error(x, phi));
            static_assert(std::same_as<decltype(left), decltype(right)>);
            REQUIRE(left == right);
        }
    }
}

TEST_CASE("probe-harness: Morphism.rename_map2") {
    // transform_error(map2(k, x, y), phi) ==
    //     map2(k, transform_error(x, phi), transform_error(y, phi))
    auto phi = renaming<set_f>(collapse{});
    auto add = [](int a, int b) { return a + b; };
    for (const auto &x : {harness::pure<set_p>(1), fail_p(-1)}) {
        for (const auto &y : {harness::pure<set_r>(2), fail_r(300)}) {
            auto left = harness::transform_error(harness::map2(add, x, y), phi);
            auto right = harness::map2(add, harness::transform_error(x, phi),
                                       harness::transform_error(y, phi));
            static_assert(std::same_as<decltype(left), decltype(right)>);
            REQUIRE(left == right);
        }
    }
}

TEST_CASE("probe-harness: Morphism.traverse_rename") {
    // transform_error(traverse(f, xs), phi) ==
    //     traverse(transform_error(f, phi), xs)
    auto phi = renaming<set_f>(collapse{});
    auto renamed_classify = [phi](int a) {
        return harness::transform_error(classify(a), phi);
    };
    for (const auto &xs :
         {std::vector<int>{}, std::vector<int>{1, 2},
          std::vector<int>{1, -1, 300}, std::vector<int>{300, -1}}) {
        auto left =
            harness::transform_error(harness::traverse(classify, xs), phi);
        auto right = harness::traverse(renamed_classify, xs);
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
    }
}

// =========================================================================
// Graded/Compose.lean -- nested carriers and flatten.
//
// `flatten` is the monadic join. Its argument is `expected<expected<T,
// Fs>, Es>` with Es and Fs distinct, so every join here is the graded
// bind's mixing point and the result grade is the union.
// =========================================================================

namespace {

using inner_r = at<int, set_r>;
using nested_pr = at<inner_r, set_p>;

auto nested_ok(int a) -> nested_pr { return nested_pr{inner_r{a}}; }
auto nested_inner_failing(int payload) -> nested_pr {
    return nested_pr{inner_r{std::unexpect, err_range{payload}}};
}
auto nested_outer_failing(int payload) -> nested_pr {
    return nested_pr{std::unexpect, err_parse{payload}};
}

/** `Graded.swap`: exchange the nesting order, keeping which layer failed. */
auto swap_layers(const nested_pr &x) -> at<at<int, set_p>, set_r> {
    using swapped = at<at<int, set_p>, set_r>;
    if (!x.has_value()) {
        return swapped{at<int, set_p>{std::unexpect, x.error()}};
    }
    if (!x->has_value()) {
        return swapped{std::unexpect, x->error()};
    }
    return swapped{at<int, set_p>{**x}};
}

} // namespace

TEST_CASE("probe-harness: Compose.flatten_map") {
    // transform(flatten(x), f) == flatten(transform(x, transform(_, f)))
    for (const auto &x :
         {nested_ok(3), nested_inner_failing(1), nested_outer_failing(2)}) {
        auto left = harness::transform(harness::flatten(x), twice);
        auto right = harness::flatten(harness::comp_map(x, twice));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(std::same_as<decltype(left), at<int, set_pr>>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: Compose.flatten_pure_outer") {
    // flatten(pure(y)) == y
    for (const auto &y : {inner_r{5}, inner_r{std::unexpect, err_range{1}}}) {
        auto flattened = harness::flatten(harness::pure<set_p>(y));
        static_assert(std::same_as<decltype(flattened), at<int, set_pr>>);
        REQUIRE(harness::equal_after_widening(flattened, y));
    }
}

TEST_CASE("probe-harness: Compose.flatten_pure_inner") {
    // flatten(transform(x, pure)) == x
    auto pure_r = [](int a) { return harness::pure<set_r>(a); };
    for (const auto &x : {harness::pure<set_p>(5), fail_p(1)}) {
        auto flattened = harness::flatten(harness::transform(x, pure_r));
        static_assert(std::same_as<decltype(flattened), at<int, set_pr>>);
        REQUIRE(harness::equal_after_widening(flattened, x));
    }
}

TEST_CASE("probe-harness: Compose.flatten_flatten") {
    // flatten(flatten(x)) == flatten(transform(x, flatten))
    // Three nested layers at three distinct grades: the left side joins
    // (p ⊔ r) ⊔ i and the right p ⊔ (r ⊔ i).
    using innermost = at<int, set_i>;
    using middle = at<innermost, set_r>;
    using outermost = at<middle, set_p>;
    auto flatten_inner = [](const middle &m) { return harness::flatten(m); };

    const outermost all_ok{middle{innermost{4}}};
    const outermost io_failing{middle{innermost{std::unexpect, err_io{3}}}};
    const outermost range_failing{middle{std::unexpect, err_range{2}}};
    const outermost parse_failing{std::unexpect, err_parse{1}};

    for (const auto &x : {all_ok, io_failing, range_failing, parse_failing}) {
        auto left = harness::flatten(harness::flatten(x));
        auto right = harness::flatten(harness::transform(x, flatten_inner));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(std::same_as<decltype(left), at<int, set_pri>>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: Compose.flatten_widen_outer") {
    // flatten(widen<Es2>(x)) == widen<Es2 | Fs>(flatten(x))
    for (const auto &x :
         {nested_ok(3), nested_inner_failing(1), nested_outer_failing(2)}) {
        auto left = harness::flatten(harness::widen<set_pi>(x));
        auto right = harness::widen<set_pri>(harness::flatten(x));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: Compose.flatten_widen_inner") {
    // flatten(transform(x, widen<Fs2>)) == widen<Es | Fs2>(flatten(x))
    auto widen_inner = [](const inner_r &inner) {
        return harness::widen<set_ri>(inner);
    };
    for (const auto &x :
         {nested_ok(3), nested_inner_failing(1), nested_outer_failing(2)}) {
        auto left = harness::flatten(harness::transform(x, widen_inner));
        auto right = harness::widen<set_pri>(harness::flatten(x));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: Compose.flatten_comm") {
    // flatten(x) == flatten(swap(x))  // up to reordering the union
    for (const auto &x :
         {nested_ok(3), nested_inner_failing(1), nested_outer_failing(2)}) {
        auto left = harness::flatten(x);
        auto right = harness::flatten(swap_layers(x));
        // {parse} ⊔ {range} against {range} ⊔ {parse}: one type.
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
    }
}

// =========================================================================
// Graded/ComposeApp.lean -- the composed applicative, grades kept nested.
// =========================================================================

TEST_CASE("probe-harness: ComposeApp.Comp.ap_pure_id") {
    // apply(pure(id), x) == x  // nested, componentwise
    auto id = [](int a) { return a; };
    auto pure_id = harness::comp_pure<set_p, set_r>(id);
    for (const auto &x :
         {nested_ok(3), nested_inner_failing(1), nested_outer_failing(2)}) {
        auto applied = harness::comp_ap(pure_id, x);
        static_assert(std::same_as<decltype(applied), nested_pr>);
        REQUIRE(applied == x);
    }
}

TEST_CASE("probe-harness: ComposeApp.Comp.ap_pure_pure") {
    // apply(pure(f), pure(a)) == pure(f(a))  // nested, componentwise
    auto applied = harness::comp_ap(harness::comp_pure<set_p, set_r>(increment),
                                    harness::comp_pure<set_p, set_r>(41));
    REQUIRE(applied == harness::comp_pure<set_p, set_r>(42));
}

TEST_CASE("probe-harness: ComposeApp.Comp.ap_interchange") {
    // apply(u, pure(a)) == apply(pure([=](auto f){ return f(a); }), u)
    auto evaluate_at_41 = [](increment_fn f) { return f(41); };
    using nested_fn = at<at<increment_fn, set_r>, set_p>;
    for (const auto &u :
         {nested_fn{at<increment_fn, set_r>{increment}},
          nested_fn{at<increment_fn, set_r>{std::unexpect, err_range{1}}},
          nested_fn{std::unexpect, err_parse{2}}}) {
        auto left = harness::comp_ap(u, harness::comp_pure<set_p, set_r>(41));
        auto right = harness::comp_ap(
            harness::comp_pure<set_p, set_r>(evaluate_at_41), u);
        static_assert(std::same_as<decltype(left), decltype(right)>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: ComposeApp.Comp.ap_comp") {
    // apply(apply(apply(pure(compose), u), v), w) == apply(u, apply(v, w))
    // Outer grades {parse}, {range}, {io} and inner grades {range}, {io},
    // {parse} across u, v, w: both layers join three distinct grades, and
    // the result is nested (p ⊔ r ⊔ i) over (r ⊔ i ⊔ p) -- one type each.
    auto compose = [](increment_fn f) {
        return
            [f](increment_fn g) { return [f, g](int x) { return f(g(x)); }; };
    };
    using u_type = at<at<increment_fn, set_r>, set_p>;
    using v_type = at<at<increment_fn, set_i>, set_r>;
    using w_type = at<at<int, set_p>, set_i>;

    auto check = [&](const u_type &u, const v_type &v, const w_type &w) {
        auto left = harness::comp_ap(
            harness::comp_ap(
                harness::comp_ap(harness::comp_pure<set_p, set_r>(compose), u),
                v),
            w);
        auto right = harness::comp_ap(u, harness::comp_ap(v, w));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(
            std::same_as<decltype(left), at<at<int, set_pri>, set_pri>>);
        REQUIRE(left == right);
        return left;
    };

    const u_type u_ok{at<increment_fn, set_r>{increment}};
    const v_type v_ok{at<increment_fn, set_i>{twice}};
    const w_type w_ok{at<int, set_p>{20}};
    REQUIRE(**check(u_ok, v_ok, w_ok) == 41);

    const u_type u_inner_failing{
        at<increment_fn, set_r>{std::unexpect, err_range{1}}};
    const v_type v_outer_failing{std::unexpect, err_range{2}};
    const w_type w_inner_failing{at<int, set_p>{std::unexpect, err_parse{3}}};
    REQUIRE(check(u_inner_failing, v_ok, w_ok)->error().holds<err_range>());
    REQUIRE(check(u_ok, v_outer_failing, w_ok).error().holds<err_range>());
    REQUIRE(check(u_ok, v_ok, w_inner_failing)->error().holds<err_parse>());
    REQUIRE(check(u_inner_failing, v_outer_failing, w_inner_failing)
                .error()
                .holds<err_range>());
}

TEST_CASE("probe-harness: ComposeApp.traverseComp_eq") {
    // traverse_comp(a -> transform(f(a), k), xs) ==
    //     transform(traverse(f, xs), ys -> traverse(k, ys))
    // f grades the outer layer at {parse, range}; k grades the inner at
    // {range}. See traverse_comp for why the left side is a hand fold.
    auto composed = [](int a) {
        return harness::transform(classify(a), to_text);
    };
    auto traverse_k = [](const std::vector<int> &ys) {
        return harness::traverse(to_text, ys);
    };
    for (const auto &xs :
         {std::vector<int>{}, std::vector<int>{1, 2, 3},
          std::vector<int>{1, -1, 3}, std::vector<int>{1, 60, 3},
          std::vector<int>{60, -1}, std::vector<int>{-1, 60}}) {
        auto left = harness::traverse_comp<set_pr, set_r>(composed, xs);
        auto right =
            harness::transform(harness::traverse(classify, xs), traverse_k);
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(
            std::same_as<decltype(left),
                         at<at<std::vector<std::string>, set_r>, set_pr>>);
        REQUIRE(left == right);
    }
}

TEST_CASE("probe-harness: ComposeApp.flatten_ap") {
    // flatten(apply(ff, xx)) == apply(flatten(ff), flatten(xx))
    //     // one-sided condition only
    // Holds when ff's outer layer fails, or ff succeeds through both
    // layers, or xx's outer layer succeeds. The excluded case is a real
    // counterexample, shown last.
    using ff_type = at<at<increment_fn, set_r>, set_p>;
    using xx_type = at<at<int, set_r>, set_i>;
    auto both = [](const ff_type &ff, const xx_type &xx) {
        auto left = harness::flatten(harness::comp_ap(ff, xx));
        auto right = harness::apply(harness::flatten(ff), harness::flatten(xx));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(std::same_as<decltype(left), at<int, set_pri>>);
        return std::pair{left, right};
    };

    const ff_type ff_ok{at<increment_fn, set_r>{increment}};
    const ff_type ff_inner_failing{
        at<increment_fn, set_r>{std::unexpect, err_range{1}}};
    const ff_type ff_outer_failing{std::unexpect, err_parse{2}};
    const xx_type xx_ok{at<int, set_r>{41}};
    const xx_type xx_inner_failing{at<int, set_r>{std::unexpect, err_range{3}}};
    const xx_type xx_outer_failing{std::unexpect, err_io{4}};

    for (const auto &xx : {xx_ok, xx_inner_failing, xx_outer_failing}) {
        auto [left, right] = both(ff_outer_failing, xx);
        REQUIRE(left == right);
    }
    for (const auto &xx : {xx_ok, xx_inner_failing, xx_outer_failing}) {
        auto [left, right] = both(ff_ok, xx);
        REQUIRE(left == right);
    }
    for (const auto &ff : {ff_ok, ff_inner_failing, ff_outer_failing}) {
        for (const auto &xx : {xx_ok, xx_inner_failing}) {
            auto [left, right] = both(ff, xx);
            REQUIRE(left == right);
        }
    }

    // The counterexample: ff fails in its INNER layer and xx in its OUTER.
    // Composed application sees ff's outer layer succeed and reaches xx's
    // failure; flattening first makes both plain failures, and the
    // short-circuit keeps ff's. Different kinds survive.
    auto [left, right] = both(ff_inner_failing, xx_outer_failing);
    REQUIRE(left != right);
    REQUIRE(left.error().holds<err_io>());
    REQUIRE(right.error().holds<err_range>());
}

// =========================================================================
// Graded/Traverse.lean -- list traversal, short-circuiting.
// =========================================================================

TEST_CASE("probe-harness: Traverse.traverse_nil") {
    // traverse(f, {}) == pure({})
    REQUIRE(harness::traverse(classify, std::vector<int>{}) ==
            harness::pure<set_pr>(std::vector<int>{}));
}

TEST_CASE("probe-harness: Traverse.traverse_cons") {
    // traverse(f, x :: xs) == map2(cons, f(x), traverse(f, xs))
    auto cons = [](int head, std::vector<int> tail) {
        tail.insert(tail.begin(), head);
        return tail;
    };
    for (int head : {1, -1, 300}) {
        for (const auto &tail :
             {std::vector<int>{}, std::vector<int>{2, 3},
              std::vector<int>{2, -2}, std::vector<int>{400}}) {
            std::vector<int> whole{head};
            whole.insert(whole.end(), tail.begin(), tail.end());
            auto left = harness::traverse(classify, whole);
            auto right = harness::map2(cons, classify(head),
                                       harness::traverse(classify, tail));
            static_assert(std::same_as<decltype(left), decltype(right)>);
            REQUIRE(left == right);
        }
    }
}

TEST_CASE("probe-harness: Traverse.traverse_map") {
    // traverse(f, transform(xs, h)) == traverse(f compose h, xs)
    auto h = [](int a) { return a - 2; };
    auto f_after_h = [&](int a) { return classify(h(a)); };
    for (const auto &xs :
         {std::vector<int>{}, std::vector<int>{3, 4}, std::vector<int>{3, 1, 4},
          std::vector<int>{3, 400}}) {
        std::vector<int> mapped;
        for (int a : xs) {
            mapped.push_back(h(a));
        }
        REQUIRE(harness::traverse(classify, mapped) ==
                harness::traverse(f_after_h, xs));
    }
}

TEST_CASE("probe-harness: Traverse.traverse_length") {
    // traverse(f, xs).value().size() == xs.size()  // shape preservation
    for (const auto &xs : {std::vector<int>{}, std::vector<int>{1},
                           std::vector<int>{1, 2, 3, 4, 5}}) {
        auto result = harness::traverse(classify, xs);
        REQUIRE(result.has_value());
        REQUIRE(result->size() == xs.size());
    }
}

namespace {

/** Whether `bt::traverse(f, xs)` is well-formed for these types. A named
 * concept, as in accumulating_object.test.cpp: a bare requires-expression
 * at block scope hard-errors instead of yielding false. */
template <class F, class T>
concept traverse_accepts = requires(F f, T xs) { bt::traverse(f, xs); };

using classify_fn = at<int, set_pr> (*)(int);
using from_empty_fn = at<int, set_none> (*)(int);
using bare_fn = int (*)(int);

} // namespace

// traverse_fromEmpty: traverse(fromEmpty, xs) == fromEmpty(xs)
// traverse_fromEmpty_map (Graded/Ungraded.lean):
//     traverse(fromEmpty compose f, xs) == fromEmpty(transform(xs, f))
//
// FINDING: neither equation has a left side here. At the empty grade the
// carrier is bare T (docs/decisions.md#empty-grade-spelling), and bare T
// is not a context, so a function returning `int` cannot be traversed.
// The explicit uniform form `expected<T, error_set<>>` is a graded
// context, but re-indexing it at its own grade yields bare T, so it
// cannot satisfy `applicative_object`'s subsumption requirement and
// `traverse` refuses it too. Both refusals are by design and both are
// pinned below. What the two Lean laws say -- that a no-fail traversal is
// a transform -- is therefore not something the C++ can get wrong: the
// only spelling available for it IS `std::ranges::transform`. The
// positive control keeps the two negatives from passing vacuously.
static_assert(traverse_accepts<classify_fn, std::vector<int>>);
static_assert(!traverse_accepts<bare_fn, std::vector<int>>);
static_assert(!traverse_accepts<from_empty_fn, std::vector<int>>);

// =========================================================================
// Graded/Tuple.lean -- heterogeneous sequencing.
//
// This library has no tuple traversable over expected; what it has is the
// n-ary `invoke`, which IS the tuple transpose: each operand at its own
// grade, one join computed at the type level. `sequence_cons` says that
// n-ary form agrees with peeling one operand off and recursing.
// =========================================================================

TEST_CASE("probe-harness: Tuple.sequence_cons") {
    // transpose(x, xs...) == map2(tuple_cons, x, transpose(xs...))
    auto tuple_of = [](const auto &...values) { return std::tuple{values...}; };
    auto tuple_cons = [](const auto &head, const auto &tail) {
        return std::tuple_cat(std::tuple{head}, tail);
    };
    auto check = [&](const at<int, set_p> &x, const at<int, set_r> &y,
                     const at<int, set_i> &z) {
        auto left =
            bt::applicative_typeclass<at<int, set_p>>.invoke(tuple_of, x, y, z);
        auto right =
            harness::map2(tuple_cons, x, harness::map2(tuple_of, y, z));
        static_assert(std::same_as<decltype(left), decltype(right)>);
        static_assert(std::same_as<decltype(left),
                                   at<std::tuple<int, int, int>, set_pri>>);
        REQUIRE(left == right);
        return left;
    };

    // Bound first and compared inside parentheses, so the tuple never meets
    // Catch's expression decomposer: on clang 19 and 20 with libstdc++ 15,
    // the tuple-like operator<=> tries to instantiate tuple_size on the
    // decomposer itself and hard-errors.
    const auto all_ok = check(harness::pure<set_p>(1), harness::pure<set_r>(2),
                              harness::pure<set_i>(3));
    REQUIRE(all_ok.has_value());
    REQUIRE((*all_ok == std::tuple{1, 2, 3}));
    REQUIRE(check(fail_p(1), harness::pure<set_r>(2), harness::pure<set_i>(3))
                .error()
                .holds<err_parse>());
    REQUIRE(check(harness::pure<set_p>(1), fail_r(2), fail_i(3))
                .error()
                .holds<err_range>());
}

// =========================================================================
// Graded/Ungraded.lean -- the same laws at one fixed error type.
//
// No error_set anywhere: `std::expected<int, std::errc>` throughout, so
// every operation takes the same-error core and nothing is joined. This is
// the model's comparison column -- what a law costs at all, before grading
// adds anything -- and it exercises the code path the graded probes above
// never reach.
// =========================================================================

namespace {

using exp_errc = std::expected<int, std::errc>;

auto errc_fail(std::errc code) -> exp_errc {
    return exp_errc{std::unexpect, code};
}
auto errc_positive(int x) -> exp_errc {
    return x > 0 ? exp_errc{x * 2} : errc_fail(std::errc::invalid_argument);
}
auto errc_small(int x) -> exp_errc {
    return x < 100 ? exp_errc{x + 1}
                   : errc_fail(std::errc::result_out_of_range);
}

} // namespace

TEST_CASE("probe-harness: Ungraded.bindF_pure_left") {
    REQUIRE(harness::and_then(exp_errc{21}, errc_positive) ==
            errc_positive(21));
    REQUIRE(harness::and_then(exp_errc{-1}, errc_positive) ==
            errc_positive(-1));
}

TEST_CASE("probe-harness: Ungraded.bindF_pure_right") {
    auto pure_errc = [](int a) { return exp_errc{a}; };
    for (const auto &x : {exp_errc{4}, errc_fail(std::errc::io_error)}) {
        REQUIRE(harness::and_then(x, pure_errc) == x);
    }
}

TEST_CASE("probe-harness: Ungraded.bindF_assoc") {
    auto rhs_continuation = [](int a) {
        return harness::and_then(errc_positive(a), errc_small);
    };
    for (const auto &x : {exp_errc{4}, exp_errc{-1}, exp_errc{60},
                          errc_fail(std::errc::io_error)}) {
        REQUIRE(harness::and_then(harness::and_then(x, errc_positive),
                                  errc_small) ==
                harness::and_then(x, rhs_continuation));
    }
}

TEST_CASE("probe-harness: Ungraded.sumEquiv_bindF") {
    // and_then(x, f) corresponds to std::expected's own and_then: the
    // probe carrier IS std::expected, so the correspondence is equality.
    for (const auto &x :
         {exp_errc{4}, exp_errc{-1}, errc_fail(std::errc::io_error)}) {
        REQUIRE(harness::and_then(x, errc_positive) ==
                x.and_then(errc_positive));
    }
}

TEST_CASE("probe-harness: Ungraded.apF_pure_id") {
    auto id = [](int a) { return a; };
    for (const auto &x : {exp_errc{4}, errc_fail(std::errc::io_error)}) {
        REQUIRE(harness::apply(std::expected<decltype(id), std::errc>{id}, x) ==
                x);
    }
}

TEST_CASE("probe-harness: Ungraded.apF_pure_pure") {
    REQUIRE(harness::apply(std::expected<increment_fn, std::errc>{increment},
                           exp_errc{41}) == exp_errc{42});
}

TEST_CASE("probe-harness: Ungraded.apF_interchange") {
    auto evaluate_at_41 = [](increment_fn f) { return f(41); };
    using fn_errc = std::expected<increment_fn, std::errc>;
    for (const auto &u :
         {fn_errc{increment}, fn_errc{std::unexpect, std::errc::io_error}}) {
        REQUIRE(harness::apply(u, exp_errc{41}) ==
                harness::apply(
                    std::expected<decltype(evaluate_at_41), std::errc>{
                        evaluate_at_41},
                    u));
    }
}

TEST_CASE("probe-harness: Ungraded.apF_comp") {
    auto compose = [](increment_fn f) {
        return
            [f](increment_fn g) { return [f, g](int x) { return f(g(x)); }; };
    };
    using fn_errc = std::expected<increment_fn, std::errc>;
    for (const auto &u :
         {fn_errc{increment}, fn_errc{std::unexpect, std::errc::io_error}}) {
        for (const auto &v :
             {fn_errc{twice},
              fn_errc{std::unexpect, std::errc::invalid_argument}}) {
            for (const auto &w :
                 {exp_errc{20}, errc_fail(std::errc::bad_message)}) {
                auto left = harness::apply(
                    harness::apply(
                        harness::apply(
                            std::expected<decltype(compose), std::errc>{
                                compose},
                            u),
                        v),
                    w);
                auto right = harness::apply(u, harness::apply(v, w));
                REQUIRE(left == right);
            }
        }
    }
}
