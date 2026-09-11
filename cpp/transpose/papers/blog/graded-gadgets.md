**DRAFT &#x2014; pending author revision**

<div class="abstract" id="org87d6c0e">
<p>
Combining an <code>expected&lt;int, errc&gt;</code> with an <code>expected&lt;int, io_errc&gt;</code> used to be ill-formed; the applicative demanded that every operand agree on the error type.
Now it compiles, and the result type is computed for you: <code>expected&lt;int, error_set&lt;errc, io_errc&gt;&gt;</code>.
The index doing the work is a <i>grade</i>: a finite set of error types under union, tracked through every composition and narrowed back down by <code>recover</code>.
This post shows the gadgets running, with the compiler checking the deductions and the program output as receipts.
The code is from <a href="https://github.com/bemanproject/transpose"><code>beman.transpose</code></a> and builds today.
</p>

</div>

**Next:** [Transpose at Work](transpose-at-work.md) &#x2014; **Up:** [Contents](index.md)


# Two libraries, two error types

Your parser fails with `std::errc`. The stream layer under it fails with `std::io_errc`. The moment one computation needs a value from each, you are hand-writing the error plumbing: a `variant`, a conversion layer, or a lowest-common-denominator error code that forgets which subsystem actually failed.

The applicative `invoke` from [earlier in this series](how-traverse-and-transpose-work.md) used to refuse this outright. Every operand had to be an `expected` with the same error type. That refusal turns out to be the opportunity: the combination was ill-formed, so giving it a meaning breaks no existing code.

```cpp
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
```

    join deduced: expected<int, error_set<errc, io_errc>>
    both ok:      15
    io failed:    holds<io_errc> = true, holds<errc> = false

The `static_assert` is the point. Nobody wrote `error_set<errc, io_errc>` at the call site; the deduction computed the union of what each operand could raise, and the failing operand kept its identity inside it.


# error\_set is a type, not a trick

The union needs a spelling, and the spelling has to not care about order. `error_set` canonicalizes at construction: the pack is sorted and deduplicated, so however two grades meet, the same set is the same type.

```cpp
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
```

```cpp
    // error_set canonicalizes: order and repetition do not create new types.
    static_assert(std::is_same_v<bt::error_set<parse_error, range_error>,
                                 bt::error_set<range_error, parse_error>>);
    static_assert(
        std::is_same_v<bt::error_set<parse_error, range_error, parse_error>,
                       bt::error_set<parse_error, range_error>>);
```

Sorting types requires ordering them, which the language does not yet provide; the implementation orders by type name as an interim stand-in for P2830 reflection-based ordering, and static-asserts that no two members render to the same name.

The value side is just as deliberate. An `error_set` value is a *witnessed subset*: one `optional` slot per member type, at most one witness each. The type says "may raise these"; a value says "did raise these", and did-raise is always a subset of may-raise. There's no discriminated union inside, and no allocation.


# The empty grade is spelled T

A plain `int` has no error types to contribute. Its grade is the empty set, and joining with the empty set is a no-op, so mixing a bare value into a graded computation leaves no trace in the deduced type.

```cpp
    using exp_sys = std::expected<int, std::errc>;
    const auto &app = bt::applicative_typeclass<exp_sys>;
    auto add = [](int a, int b) { return a + b; };

    // A bare int is empty-graded: joining with the empty set is a no-op, so
    // the result is still expected<int, errc> -- the carrier spelling never
    // acquires a singleton error_set it did not need.
    auto result = app.invoke(add, exp_sys{37}, 5);
    static_assert(std::is_same_v<decltype(result), exp_sys>);
    std::cout << "bare operand: expected<int, errc> = " << *result << '\n';
```

    bare operand: expected<int, errc> = 42

This is what keeps grading additive rather than viral. An unmixed pipeline of `expected<T, E>` never acquires an `error_set<E>` in its spelling; the singleton set exists at the type-bookkeeping level, but the carrier keeps the type you wrote. Code that never mixes error types never sees any of this.


# Two composition disciplines

When several operands fail, what should the error be? The default object keeps the answer `expected` has always given: the leftmost failure wins and the rest are never examined. A second object, reached through `accumulating_applicative_typeclass`, visits every operand and keeps one witness per distinct error type.

```cpp
using exp_mixed = std::expected<int, bt::error_set<parse_error, range_error>>;

auto bad_parse(int at) -> exp_mixed {
    return exp_mixed{std::unexpect, parse_error{at}};
}
auto bad_range(int v) -> exp_mixed {
    return exp_mixed{std::unexpect, range_error{v}};
}
```

```cpp
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
```

    short-circuit: holds<parse_error> = true, holds<range_error> = false
    accumulating:  witness_count = 2
      parse_error at position 12
      range_error with value 99

The accumulated `error_set` value *is* the evidence; there is no side channel of diagnostics. And the accumulating object has no `bind`. Sequencing needs the first computation's value to feed the continuation, and there isn't one when that computation failed; asking for it is a compile error whose message says so.


# recover narrows the grade

Grades widen at every mixing point, so there had better be a way back down. `recover<E...>` handles the named alternatives and subtracts them from the grade: handle one member and the set shrinks, handle all of them and you are left holding a plain value.

```cpp
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
```

    recovered parse_error; still failing with range_error: true
    recovered everything; plain int = 0

The same set-difference happens at both levels. The type loses the handled members; the value loses their witnesses. And the empty grade is spelled `int`, not `expected<int, error_set<>>`, so fully recovering really does hand you back an ordinary value.


# Over a whole traversal

The gadgets compose with the rest of the library. `traverse` maps a fallible function over a vector and transposes the failures out; the grade of the per-element function becomes the grade of the whole traversal, and the accumulating object slots in as an ordinary trailing argument.

```cpp
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
```

    all ok: [2, 4, 6]
    accumulated over the traversal: witness_count = 2
      parse_error at position -7
      range_error with value 500

One pass over the data, every distinct failure collected, and the result type says so.


# Where the idea comes from

Indexing a computation's type by an effect drawn from an ordered monoid is Katsumata's parametric effect monads (Shin-ya Katsumata, 2014); the applicative side of the family goes back to McBride and Paterson (Conor McBride and Ross Paterson, 2008). Here the algebra is a bounded join-semilattice: finite sets of types, union as join, the empty set as bottom, subset as the order. The framework layer is written against that algebra and nothing else (a `grade_semilattice` concept, join, bottom, and a subsumption order), with `error_set` as one model.

A second, deliberately trivial model (a two-point lattice, "never fails" and "may fail") lives in the test suite as a leak detector. Any place the framework secretly assumes it is talking about errors, the two-point model fails to slide in, and it caught a real one during development. The semilattice laws themselves are checked by a `consteval` harness, once per model, instead of being restated in every constraint.

The laws are cheap to state and the gadgets are small. What they buy is a compiler that tracks which errors a composition can raise, per composition, with no annotations on the happy path. I didn't expect the whole thing to fit in three headers.

Conor McBride and Ross Paterson (2008). *Applicative Programming with Effects*, Journal of Functional Programming.

Shin-ya Katsumata (2014). *Parametric Effect Monads and Semantics of Effect Systems*.
