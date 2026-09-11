// examples/traverse_post_example.cpp                                 -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// How it all really works: traverse maps a context-producing function over a
// structure and transposes the effects; transpose is traverse with the
// identity function; the context's applicative object supplies pure and
// invoke. Companion example for the "Traverse" blog post; run with a section
// name (traverse, context, identity, applicative) to print just that section,
// or with no arguments to run them all.
//
// The `// <uuid>` ... `// <uuid> end` comment pairs are org-transclusion
// anchors used by papers/blog/*.org; do not delete or nest them.

#include <beman/transpose/transpose.hpp>

#include <expected>
#include <iostream>
#include <optional>
#include <string_view>
#include <system_error>
#include <vector>

namespace bt = beman::transpose;

namespace {

void print_ints(std::string_view label, const std::vector<int> &values) {
    std::cout << label << "[";
    for (std::size_t i = 0; i < values.size(); ++i) {
        std::cout << (i ? ", " : "") << values[i];
    }
    std::cout << "]\n";
}

// 7fbe2092-2dc3-499e-aeb7-2ad36826be76
/** Half of an even number; nothing for an odd one. */
auto halve(int x) -> std::optional<int> {
    if (x % 2 == 0) {
        return x / 2;
    }
    return std::nullopt;
}
// 7fbe2092-2dc3-499e-aeb7-2ad36826be76 end

void traverse_section() {
    // a62a5add-27fc-4491-b242-e39f21029abe
    // traverse applies halve at every position and transposes the resulting
    // optionals into one optional around the whole vector.
    auto all_even = bt::traverse(halve, std::vector<int>{2, 4, 6});
    static_assert(
        std::is_same_v<decltype(all_even), std::optional<std::vector<int>>>);
    std::cout << "all even: has_value = " << std::boolalpha
              << all_even.has_value() << '\n';

    auto one_odd = bt::traverse(halve, std::vector<int>{2, 3, 6});
    std::cout << "one odd:  has_value = " << one_odd.has_value() << '\n';
    // a62a5add-27fc-4491-b242-e39f21029abe end

    if (all_even) {
        print_ints("halved:   ", *all_even);
    }
}

void context_section() {
    // 4e59fcf2-1ec2-4568-858f-836533f9fe89
    // The applicative context is whatever the function returns. Same
    // traversal, same structure; a function returning expected instead of
    // optional swaps in a different context -- nothing else changes.
    auto checked = [](int x) -> std::expected<int, std::errc> {
        if (x % 2 == 0) {
            return x / 2;
        }
        return std::unexpected{std::errc::invalid_argument};
    };

    auto result = bt::traverse(checked, std::vector<int>{2, 3, 6});
    static_assert(std::is_same_v<decltype(result),
                                 std::expected<std::vector<int>, std::errc>>);
    std::cout << "expected context: has_value = " << std::boolalpha
              << result.has_value() << '\n';
    // 4e59fcf2-1ec2-4568-858f-836533f9fe89 end
}

void identity_section() {
    // 5160d30d-ab74-4fa8-8370-4c784b8b085c
    std::vector<std::optional<int>> maybes{1, 2, 3};

    // transpose is traverse with the identity function: hand traverse a
    // function that returns its argument unchanged and the "map" step
    // disappears, leaving only the transposition of effects.
    auto via_traverse =
        bt::traverse([](const std::optional<int> &x) { return x; }, maybes);
    auto via_transpose = bt::transpose(maybes);

    static_assert(
        std::is_same_v<decltype(via_traverse), decltype(via_transpose)>);
    std::cout << "traverse(identity) == transpose: " << std::boolalpha
              << (via_traverse == via_transpose) << '\n';
    // 5160d30d-ab74-4fa8-8370-4c784b8b085c end
}

void applicative_section() {
    // e0374a39-17e5-464f-b2bf-792c698fbe46
    // The applicative object is the whole interface traverse needs from a
    // context: pure lifts a plain value in, invoke applies a plain function
    // across contextual arguments.
    const auto &app = bt::applicative_typeclass<std::optional<int>>;

    auto lifted = app.pure(7);
    std::cout << "pure(7): " << *lifted << '\n';

    auto sum = app.invoke([](int a, int b) { return a + b; },
                          std::optional<int>{3}, std::optional<int>{4});
    std::cout << "invoke(add, {3}, {4}): " << *sum << '\n';

    auto absent = app.invoke([](int a, int b) { return a + b; },
                             std::optional<int>{3}, std::optional<int>{});
    std::cout << "invoke(add, {3}, {}): has_value = " << std::boolalpha
              << absent.has_value() << '\n';
    // e0374a39-17e5-464f-b2bf-792c698fbe46 end
}

struct section {
    std::string_view name;
    void (*run)();
};

constexpr section sections[] = {
    {"traverse", traverse_section},
    {"context", context_section},
    {"identity", identity_section},
    {"applicative", applicative_section},
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
