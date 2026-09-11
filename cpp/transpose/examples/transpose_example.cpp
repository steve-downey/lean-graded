// examples/transpose_example.cpp                                     -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Paper A in one screen: a single `transpose` front door flips
//   structure<context<T>>  ->  context<structure<T>>
// for three independent contexts, all over the same std::vector structure.

#include <beman/transpose/transpose.hpp>

#include <iostream>
#include <optional>
#include <vector>

namespace bt = beman::transpose;

int main() {
    // Domain 1 — fallible value: vector<optional<T>> -> optional<vector<T>>.
    std::vector<std::optional<int>> maybe{
        std::optional<int>{1}, std::optional<int>{2}, std::optional<int>{3}};
    if (auto all = bt::transpose(maybe)) {
        std::cout << "optional: got " << all->size() << " values\n";
    }

    // Domain 2 — deferred result: vector<sender<T>> -> sender<vector<T>>.
    std::vector<bt::sender<int>> senders{bt::sender<int>::ready(10),
                                         bt::sender<int>::ready(20),
                                         bt::sender<int>::ready(30)};
    auto composed = bt::transpose(senders); // nothing runs yet
    auto values = composed.get();           // now it runs
    std::cout << "sender: ran to produce " << values.size() << " values\n";

    // Domain 3 — lanewise / SIMD: vector<zip_list<T>> -> zip_list<vector<T>>.
    std::vector<bt::zip_list<int>> lanes{bt::zip_list<int>{{1, 2}},
                                         bt::zip_list<int>{{10, 20}},
                                         bt::zip_list<int>{{100, 200}}};
    auto transposed = bt::transpose(lanes);
    std::cout << "zip_list: " << transposed.data.size() << " lanes of "
              << transposed.data.front().size() << " elements\n";

    return 0;
}
