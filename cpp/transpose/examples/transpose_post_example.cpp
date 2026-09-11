// examples/transpose_post_example.cpp                                -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// One verb, three contexts: transpose flips structure<context<T>> into
// context<structure<T>> for optional (fallible values), sender (deferred
// work), and simd lanes (data parallelism). Companion example for the
// "Transpose" blog post; run with a section name (optional, sender, simd) to
// print just that section, or with no arguments to run them all.
//
// The `// <uuid>` ... `// <uuid> end` comment pairs are org-transclusion
// anchors used by papers/blog/*.org; do not delete or nest them.

#include <beman/transpose/transpose.hpp>

#include <iostream>
#include <optional>
#include <string_view>
#include <vector>
#include <version>

namespace bt = beman::transpose;

namespace {

void print_ints(std::string_view label, const std::vector<int> &values) {
    std::cout << label << "[";
    for (std::size_t i = 0; i < values.size(); ++i) {
        std::cout << (i ? ", " : "") << values[i];
    }
    std::cout << "]\n";
}

void optional_section() {
    // 05ce0358-d2a6-4908-a5b3-ec09da449bbd
    // Every position present: the vector of maybes becomes maybe-a-vector.
    std::vector<std::optional<int>> complete{1, 2, 3};
    std::optional<std::vector<int>> all = bt::transpose(complete);
    std::cout << "complete input:  has_value = " << std::boolalpha
              << all.has_value() << '\n';

    // One gap anywhere and the whole result is empty -- the absence is
    // hoisted out of the structure, not left inside it.
    std::vector<std::optional<int>> gapped{1, std::nullopt, 3};
    std::optional<std::vector<int>> none = bt::transpose(gapped);
    std::cout << "gapped input:    has_value = " << none.has_value() << '\n';
    // 05ce0358-d2a6-4908-a5b3-ec09da449bbd end

    if (all) {
        print_ints("transposed:      ", *all);
    }
}

void sender_section() {
    // 680950c9-7c4f-4aac-9e7b-bd32d9c7056a
    // Each sender defers a computation; running one announces itself.
    auto deferred = [](int value) {
        return bt::sender<int>{[value] {
            std::cout << "  running the sender for " << value << '\n';
            return value * value;
        }};
    };
    std::vector<bt::sender<int>> senders{deferred(1), deferred(2), deferred(3)};

    auto composed = bt::transpose(senders);
    std::cout << "composed vector<sender<int>> into sender<vector<int>>; "
                 "nothing has run yet\n";

    std::vector<int> values = composed.get();
    std::cout << "after get():\n";
    // 680950c9-7c4f-4aac-9e7b-bd32d9c7056a end
    print_ints("  ", values);
}

// __has_include(<simd>) alone is not enough: libstdc++ ships the <simd>
// header unconditionally but leaves it empty unless the toolchain also
// supports expansion statements (P1306), so check its readiness macro too.
#if __has_include(<simd>) && __cplusplus > 202302L && defined(__glibcxx_simd)

void simd_section() {
    // e916da84-685b-40b3-aee5-c9df63321855
    constexpr int W = 4;
    using vec4 = std::simd::vec<int, W>;

    // Three W-wide computations, one per structure position, filled from
    // real std::simd arithmetic.
    vec4 a([](int lane) { return lane + 1; });        // {1, 2, 3, 4}
    vec4 b([](int lane) { return (lane + 1) * 10; }); // {10, 20, 30, 40}
    vec4 c([](int lane) { return (lane + 1) * 100; });

    std::vector<bt::simd_lanes<int, W>> structure(3);
    for (int lane = 0; lane < W; ++lane) {
        structure[0].data[lane] = a[lane];
        structure[1].data[lane] = b[lane];
        structure[2].data[lane] = c[lane];
    }

    // vector<simd_lanes<int, W>> -> simd_lanes<vector<int>, W>: W complete
    // result vectors, one per hardware lane.
    auto transposed = bt::transpose(structure);
    // e916da84-685b-40b3-aee5-c9df63321855 end

    std::cout << "3 positions x " << W << " lanes -> " << W
              << " lanes of vector<int>\n";
    for (int lane = 0; lane < W; ++lane) {
        std::cout << "  lane " << lane << ": ";
        print_ints("", transposed.data[lane]);
    }
}

#else // std::simd (P1928, C++26) unavailable in this configuration

void simd_section() {
    std::cout << "std::simd (P1928, C++26) is unavailable in this "
                 "configuration; simd section skipped.\n";
}

#endif

struct section {
    std::string_view name;
    void (*run)();
};

constexpr section sections[] = {
    {"optional", optional_section},
    {"sender", sender_section},
    {"simd", simd_section},
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
