// examples/graded_gadgets_example.cpp                                -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Graded gadgets: mixing distinct error types at an applicative mixing point
// joins their grades into one error_set; recover narrows the grade back down.
// Companion example for the "Graded Gadgets" blog post; run with a section
// name (mixing, lazy-join, canonical, accumulate, recover, traverse) to print
// just that section, or with no arguments to run them all.
//
// The `// <uuid>` ... `// <uuid> end` comment pairs are org-transclusion
// anchors used by papers/blog/*.org; do not delete or nest them.

#include <beman/transpose/transpose.hpp>

#include <expected>
#include <iostream>
#include <string_view>
#include <system_error>
#include <vector>

namespace bt = beman::transpose;

// Named error types with external linkage and a stable spelling, as the
// interim type ordering in error_set.hpp requires.
namespace graded_gadgets {

// 70faaeb2-f44d-44d8-8fdc-abf8ce74d7ef
struct parse_error {
    int position{};

    friend auto operator==(const parse_error &, const parse_error &)
        -> bool = default;
};
struct range_error {
    int value{};

    friend auto operator==(const range_error &, const range_error &)
        -> bool = default;
};
// 70faaeb2-f44d-44d8-8fdc-abf8ce74d7ef end

} // namespace graded_gadgets

using graded_gadgets::parse_error;
using graded_gadgets::range_error;

namespace {

void mixing() {
    // c74dfc6a-4ae4-4f21-82fa-2097a17d8b87
    using exp_sys = std::expected<int, std::errc>;
    using exp_io = std::expected<int, std::io_errc>;

    const auto &app = bt::applicative_typeclass<exp_sys>;
    auto add = [](int a, int b) { return a + b; };

    // Two operands, two DIFFERENT error types. Before grading this call was
    // ill-formed; now the deduced error type is the join of the two grades.
    auto both_ok = app.invoke(add, exp_sys{5}, exp_io{10});
    static_assert(std::is_same_v<
                  decltype(both_ok),
                  std::expected<int, bt::error_set<std::errc, std::io_errc>>>);
    std::cout << "join deduced: expected<int, error_set<errc, io_errc>>\n";
    std::cout << "both ok:      " << *both_ok << '\n';

    // A failing operand widens into the joined set, keeping its identity.
    auto io_failed = app.invoke(add, exp_sys{5},
                                exp_io{std::unexpect, std::io_errc::stream});
    std::cout << "io failed:    holds<io_errc> = " << std::boolalpha
              << io_failed.error().holds<std::io_errc>()
              << ", holds<errc> = " << io_failed.error().holds<std::errc>()
              << '\n';
    // c74dfc6a-4ae4-4f21-82fa-2097a17d8b87 end
}

void lazy_join() {
    // a1b0528a-16f7-4a62-9ae8-684b05fbc8ed
    using exp_sys = std::expected<int, std::errc>;
    const auto &app = bt::applicative_typeclass<exp_sys>;
    auto add = [](int a, int b) { return a + b; };

    // A bare int is empty-graded: joining with the empty set is a no-op, so
    // the result is still expected<int, errc> -- the carrier spelling never
    // acquires a singleton error_set it did not need.
    auto result = app.invoke(add, exp_sys{37}, 5);
    static_assert(std::is_same_v<decltype(result), exp_sys>);
    std::cout << "bare operand: expected<int, errc> = " << *result << '\n';
    // a1b0528a-16f7-4a62-9ae8-684b05fbc8ed end
}

void canonical() {
    // 5c70a8c3-c9d4-433d-9f11-2c433cfef7df
    // error_set canonicalizes: order and repetition do not create new types.
    static_assert(std::is_same_v<bt::error_set<parse_error, range_error>,
                                 bt::error_set<range_error, parse_error>>);
    static_assert(
        std::is_same_v<bt::error_set<parse_error, range_error, parse_error>,
                       bt::error_set<parse_error, range_error>>);
    // 5c70a8c3-c9d4-433d-9f11-2c433cfef7df end
    std::cout << "error_set<parse,range> == error_set<range,parse>: "
                 "same type, checked at compile time\n";
}

// ae466cba-1a93-4a1d-b148-497958a86145
using exp_mixed = std::expected<int, bt::error_set<parse_error, range_error>>;

auto bad_parse(int at) -> exp_mixed {
    return exp_mixed{std::unexpect, parse_error{at}};
}
auto bad_range(int v) -> exp_mixed {
    return exp_mixed{std::unexpect, range_error{v}};
}
// ae466cba-1a93-4a1d-b148-497958a86145 end

void accumulate() {
    auto add = [](int a, int b) { return a + b; };

    // 045991c1-1dd4-4f93-af8a-b3ac53ce7702
    // The default object short-circuits: the leftmost failure wins and the
    // rest are never examined.
    const auto &short_circuit = bt::applicative_typeclass<exp_mixed>;
    auto first_only = short_circuit.invoke(add, bad_parse(12), bad_range(99));
    std::cout << "short-circuit: holds<parse_error> = " << std::boolalpha
              << first_only.error().holds<parse_error>()
              << ", holds<range_error> = "
              << first_only.error().holds<range_error>() << '\n';

    // The accumulating object visits every operand and keeps one witness per
    // distinct error type: the error_set VALUE is the evidence.
    const auto &accumulating =
        bt::accumulating_applicative_typeclass<exp_mixed>;
    auto both = accumulating.invoke(add, bad_parse(12), bad_range(99));
    std::cout << "accumulating:  witness_count = "
              << both.error().witness_count() << '\n';
    std::cout << "  parse_error at position "
              << both.error().witness<parse_error>()->position << '\n';
    std::cout << "  range_error with value "
              << both.error().witness<range_error>()->value << '\n';
    // 045991c1-1dd4-4f93-af8a-b3ac53ce7702 end
}

void recover() {
    auto add = [](int a, int b) { return a + b; };
    const auto &accumulating =
        bt::accumulating_applicative_typeclass<exp_mixed>;
    auto both = accumulating.invoke(add, bad_parse(12), bad_range(99));

    // fb4194b2-a5cf-43eb-bed8-d50c09601efd
    // recover<parse_error> consumes that alternative and the grade narrows:
    // {parse_error, range_error} minus {parse_error} is {range_error}.
    auto narrowed = bt::recover<parse_error>(
        both, [](const parse_error &e) { return e.position; });
    static_assert(
        std::is_same_v<decltype(narrowed),
                       std::expected<int, bt::error_set<range_error>>>);
    std::cout << "recovered parse_error; still failing with range_error: "
              << std::boolalpha << narrowed.error().holds<range_error>()
              << '\n';

    // Handling every member empties the grade, and an empty grade is spelled
    // as the BARE value type -- not expected<int, error_set<>>.
    auto recovered = bt::recover<parse_error, range_error>(
        both, [](const auto &) { return 0; });
    static_assert(std::is_same_v<decltype(recovered), int>);
    std::cout << "recovered everything; plain int = " << recovered << '\n';
    // fb4194b2-a5cf-43eb-bed8-d50c09601efd end
}

void traverse() {
    // 8ec1b0e5-e4e8-4dbb-8644-6293fc959e42
    auto classify = [](int x) -> exp_mixed {
        if (x < 0) {
            return bad_parse(x);
        }
        if (x > 99) {
            return bad_range(x);
        }
        return exp_mixed{x * 2};
    };

    // traverse transposes vector<int> -> expected<vector<int>, error_set<...>>,
    // short-circuiting at the first failure by default.
    auto all_ok = bt::traverse(classify, std::vector<int>{1, 2, 3});
    static_assert(
        std::is_same_v<decltype(all_ok),
                       std::expected<std::vector<int>,
                                     bt::error_set<parse_error, range_error>>>);
    std::cout << "all ok: [";
    for (std::size_t i = 0; i < all_ok->size(); ++i) {
        std::cout << (i ? ", " : "") << (*all_ok)[i];
    }
    std::cout << "]\n";

    // The trailing policy argument swaps in the accumulating object; the
    // call site is otherwise identical, and now every distinct failure in
    // the traversal is collected.
    auto collected =
        bt::traverse(classify, std::vector<int>{1, -7, 500, 3},
                     bt::accumulating_applicative_typeclass<exp_mixed>);
    std::cout << "accumulated over the traversal: witness_count = "
              << collected.error().witness_count() << '\n';
    std::cout << "  parse_error at position "
              << collected.error().witness<parse_error>()->position << '\n';
    std::cout << "  range_error with value "
              << collected.error().witness<range_error>()->value << '\n';
    // 8ec1b0e5-e4e8-4dbb-8644-6293fc959e42 end
}

struct section {
    std::string_view name;
    void (*run)();
};

constexpr section sections[] = {
    {"mixing", mixing},       {"lazy-join", lazy_join},
    {"canonical", canonical}, {"accumulate", accumulate},
    {"recover", recover},     {"traverse", traverse},
};

} // namespace

int main(int argc, char **argv) {
    if (argc < 2) {
        for (const auto &s : sections) {
            std::cout << "== " << s.name << " ==\n";
            s.run();
        }
        return 0;
    }
    for (int i = 1; i < argc; ++i) {
        for (const auto &s : sections) {
            if (s.name == argv[i]) {
                s.run();
            }
        }
    }
    return 0;
}
