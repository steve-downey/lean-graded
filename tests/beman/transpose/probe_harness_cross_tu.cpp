// tests/beman/transpose/probe_harness_cross_tu.cpp                   -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

// The second translation unit of the probe harness. It exists to make one
// claim that no static_assert can make: that two translation units which
// spell an error_set's pack in different orders agree on the TYPE, so that
// a function declared with one spelling and defined with the other links.
// The declarations are in probe_harness.test.cpp; the packs here are
// deliberately permuted and, for the second, duplicated. If
// canonicalization ever produced spelling-dependent types, the mangled
// names would differ and the test binary would fail to link -- which is
// the cross-TU half of the Lean side's `joinAll_perm` / `joinAll_dedup`
// obligations (docs/probe-harness.md in steve-downey/lean-graded).

#include <beman/transpose/error_set.hpp>

#include <expected>

namespace bt = beman::transpose;

namespace beman_transpose_lean_probes {

// Redeclared here, not shared through a header: sharing one declaration
// would make the two TUs agree by construction and prove nothing.
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

// Declared in probe_harness.test.cpp as <err_io, err_parse, err_range>.
auto cross_tu_permuted(
    const std::expected<int, bt::error_set<err_parse, err_range, err_io>> &x)
    -> int;

// Declared in probe_harness.test.cpp as <err_parse, err_range>.
auto cross_tu_deduplicated(
    const std::expected<int, bt::error_set<err_parse, err_range, err_parse>> &x)
    -> int;

auto cross_tu_permuted(
    const std::expected<int, bt::error_set<err_parse, err_range, err_io>> &x)
    -> int {
    return x.has_value() ? *x : -1;
}

auto cross_tu_deduplicated(
    const std::expected<int, bt::error_set<err_parse, err_range, err_parse>> &x)
    -> int {
    return x.has_value() ? *x : -1;
}

} // namespace beman_transpose_lean_probes
