// examples/soa_aos_example.cpp                                       -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// SoA <-> AoS transposition: tuple<array<T, N>...> -> array<tuple<T...>, N>
//
// This is the classic "structure of arrays" to "array of structures" transform.
// The structure is std::tuple (heterogeneous), and the context is std::array
// (fixed-width positional). The applicative for array is the same positional
// semantics as zip_list / simd_lanes, and transpose_tuple provides the
// heterogeneous traversal that std::tuple requires (since it cannot use the
// homogeneous Traversable loop).

#include <beman/transpose/transpose.hpp>

#include <array>
#include <iostream>
#include <string>
#include <tuple>

namespace bt = beman::transpose;

int main() {
    // --- SoA layout: each field stored contiguously (column-major).
    // Good for vectorized per-field processing.
    std::tuple soa{
        std::array<int, 4>{1, 2, 3, 4},
        std::array<double, 4>{1.1, 2.2, 3.3, 4.4},
        std::array<char, 4>{'a', 'b', 'c', 'd'},
    };

    // --- Transpose to AoS: each record stored as a complete tuple (row-major).
    // Good for per-record access patterns.
    auto aos = bt::transpose_tuple(soa);

    std::cout << "tuple<array<int,4>, array<double,4>, array<char,4>>\n"
              << "  -> array<tuple<int, double, char>, 4>\n\n";
    for (std::size_t i = 0; i < aos.size(); ++i) {
        auto &[id, value, tag] = aos[i];
        std::cout << "  record " << i << ": {" << id << ", " << value << ", '"
                  << tag << "'}\n";
    }

    // --- Also works with duplicate types in the tuple.
    std::tuple dup{
        std::array<int, 3>{10, 20, 30},
        std::array<int, 3>{100, 200, 300},
    };
    auto dup_aos = bt::transpose_tuple(dup);

    std::cout
        << "\ntuple<array<int,3>, array<int,3>> -> array<tuple<int,int>, 3>\n";
    for (std::size_t i = 0; i < dup_aos.size(); ++i) {
        auto &[a, b] = dup_aos[i];
        std::cout << "  [" << i << "] = {" << a << ", " << b << "}\n";
    }

    // --- The array applicative also works standalone for lanewise computation.
    const auto &app = bt::applicative_typeclass<std::array<int, 4>>;
    std::array<int, 4> xs{1, 2, 3, 4};
    std::array<int, 4> ys{10, 20, 30, 40};
    auto sums = app.invoke([](int x, int y) { return x + y; }, xs, ys);

    std::cout << "\narray applicative invoke (+): [";
    for (std::size_t i = 0; i < sums.size(); ++i) {
        if (i > 0)
            std::cout << ", ";
        std::cout << sums[i];
    }
    std::cout << "]\n";

    return 0;
}
