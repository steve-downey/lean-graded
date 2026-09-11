// examples/simd_example.cpp                                          -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Paper A's SIMD domain with real hardware: std::simd::vec (GCC 16 / P1928)
// provides the concrete lanewise context, while the same `transpose` and
// `traverse` front door handles the structural plumbing.
//
// Domain: vector<simd_lanes<T, N>> -> simd_lanes<vector<T>, N>
//   Each structure position holds an N-wide SIMD computation; transposition
//   yields N complete structures, one per hardware lane.

#include <version>

// __has_include(<simd>) alone is not enough: libstdc++ ships the <simd>
// header unconditionally but leaves it empty unless the toolchain also
// supports expansion statements (P1306), so check its readiness macro too.
#if __has_include(<simd>) && __cplusplus > 202302L && defined(__glibcxx_simd)

#include <beman/transpose/transpose.hpp>

#include <simd>

#include <iostream>
#include <vector>

namespace bt = beman::transpose;

int main() {
    constexpr int W = 4;
    using vec4 = std::simd::vec<int, W>;

    // --- transpose: vector<simd_lanes<int, W>> -> simd_lanes<vector<int>, W>
    //
    // Build three simd_lanes from std::simd::vec arithmetic.
    // Think: three data-parallel computations (one per structure position),
    // each producing W results simultaneously.

    vec4 sa([](int i) { return i + 1; });         // {1, 2, 3, 4}
    vec4 sb([](int i) { return (i + 1) * 10; });  // {10, 20, 30, 40}
    vec4 sc([](int i) { return (i + 1) * 100; }); // {100, 200, 300, 400}

    // Transfer from hardware SIMD registers into the applicative context.
    bt::simd_lanes<int, W> lane_a, lane_b, lane_c;
    for (int i = 0; i < W; ++i) {
        lane_a.data[i] = sa[i];
        lane_b.data[i] = sb[i];
        lane_c.data[i] = sc[i];
    }

    std::vector<bt::simd_lanes<int, W>> structure{lane_a, lane_b, lane_c};
    auto transposed = bt::transpose(structure);

    std::cout << "transpose: " << structure.size() << " simd_lanes<int," << W
              << "> -> " << transposed.width << " lanes of vector<int>\n";
    for (int lane = 0; lane < W; ++lane) {
        std::cout << "  lane " << lane << ": [";
        for (std::size_t j = 0; j < transposed.data[lane].size(); ++j) {
            if (j > 0)
                std::cout << ", ";
            std::cout << transposed.data[lane][j];
        }
        std::cout << "]\n";
    }

    // --- traverse: apply a SIMD-producing function, then transpose.
    //
    // Scale each coefficient by lane index using std::simd::vec arithmetic.
    // traverse(f, vector<int>) -> simd_lanes<vector<int>, W>

    std::vector<int> coefficients{3, 5, 7};

    auto scale_by_lane = [](int coeff) -> bt::simd_lanes<int, W> {
        bt::simd_lanes<int, W> result;
        vec4 lanes([coeff](int lane) { return coeff * (lane + 1); });
        for (int i = 0; i < W; ++i)
            result.data[i] = lanes[i];
        return result;
    };

    auto scaled = bt::traverse(scale_by_lane, coefficients);

    std::cout << "\ntraverse: scaled " << coefficients.size()
              << " coefficients across " << W << " SIMD lanes\n";
    for (int lane = 0; lane < W; ++lane) {
        std::cout << "  lane " << lane << " (" << (lane + 1) << "x): [";
        for (std::size_t j = 0; j < scaled.data[lane].size(); ++j) {
            if (j > 0)
                std::cout << ", ";
            std::cout << scaled.data[lane][j];
        }
        std::cout << "]\n";
    }

    return 0;
}

#else // std::simd (P1928, C++26) unavailable in this configuration

#include <iostream>

int main() {
    std::cout << "std::simd (P1928, C++26) is unavailable in this "
                 "configuration; simd_example skipped.\n";
    return 0;
}

#endif
