**DRAFT &#x2014; pending author revision**

<div class="abstract" id="org97815f0">
<p>
<a href="transpose-at-work.html">The previous post</a> ran <code>transpose</code> over three contexts and ended on a claim: <code>transpose</code> is <code>traverse</code> with the identity function.
This post makes the claim concrete with running code.
<code>traverse</code> maps a context-producing function over a structure and transposes the effects as it goes; the context is deduced from the function's return type; and the whole contract a context must satisfy is an applicative object with <code>pure</code> and <code>invoke</code>.
That pair of ideas is McBride and Paterson's applicative functor and Gibbons and Oliveira's iterator, wearing C++23 clothes.
</p>

</div>

**Prev:** [Transpose at Work](transpose-at-work.md) &#x2014; **Up:** [Contents](index.md)


# One function, applied under effects

Start with `traverse` doing something `transpose` can not: mapping while it walks. `halve` produces a value only for even input.

```cpp
/** Half of an even number; nothing for an odd one. */
auto halve(int x) -> std::optional<int> {
    if (x % 2 == 0) {
        return x / 2;
    }
    return std::nullopt;
}
```

```cpp
    // traverse applies halve at every position and transposes the resulting
    // optionals into one optional around the whole vector.
    auto all_even = bt::traverse(halve, std::vector<int>{2, 4, 6});
    static_assert(
        std::is_same_v<decltype(all_even), std::optional<std::vector<int>>>);
    std::cout << "all even: has_value = " << std::boolalpha
              << all_even.has_value() << '\n';

    auto one_odd = bt::traverse(halve, std::vector<int>{2, 3, 6});
    std::cout << "one odd:  has_value = " << one_odd.has_value() << '\n';
```

    all even: has_value = true
    one odd:  has_value = false
    halved:   [1, 2, 3]

One walk. Each element is mapped through `halve`, and the per-element `optional` s are combined into a single `optional` around the rebuilt vector. Mapping first and transposing second would allocate an intermediate `vector<optional<int>>`; `traverse` fuses the two.


# The context is the return type

Nothing in that call named `optional`. `traverse` deduces the context by asking what the function returns for one element, then looks up `applicative_typeclass` for that type. Change the function's return type and a different context's rules apply; the traversal does not change.

```cpp
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
```

    expected context: has_value = false

The deduction in the library is what you'd write by hand:

```cpp
using Context =
    remove_cvref_t<std::invoke_result_t<F, const element_type &>>;
const auto &applicative = applicative_typeclass<Context>;
```


# transpose is traverse with identity

Now the claim from last time. If the elements already *are* contextual values, there is nothing to map; hand `traverse` a function that returns its argument unchanged and only the effect-combining remains.

```cpp
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
```

    traverse(identity) == transpose: true

And that's not an analogy; it's the implementation. Every Traversable instance in the library supplies `traverse` and inherits `transpose` from the CRTP base, which derives it in four lines:

```cpp
template <class T>
auto transpose(this auto &&self, T &&value) {
    using Context = element_type;
    const auto &applicative = applicative_typeclass<Context>;
    return self.traverse(
        applicative, [](auto &&x) { return std::forward<decltype(x)>(x); },
        std::forward<T>(value));
}
```

The only difference from the general case is where the context comes from: `transpose` reads it off the element type, since the identity function's return type is its argument type. McBride and Paterson call this `dist`, the distributive law, and derive it from `traverse` the same way (Conor McBride and Ross Paterson, 2008).


# The applicative object is the whole interface

Everything above leans on one object per context. What does a context actually have to provide? Two things: `pure`, which lifts a plain value in, and `invoke`, which applies a plain function across contextual arguments.

```cpp
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
```

    pure(7): 7
    invoke(add, {3}, {4}): 7
    invoke(add, {3}, {}): has_value = false

That is the entire vocabulary `traverse` uses: `pure` for the empty structure, `invoke` to prepend each mapped element to the accumulating result. Haskell spells the second operation `<*>`, one function-in-a-context applied to one value-in-a-context. The library makes n-ary `invoke` the interface instead, and for a reason that only shows up when the context gets interesting: for `std::simd`, a register of callables is not a type you can spell, so `ap` has no signature there. Currying is an encoding detail; applying a function to several independent contextual arguments is the operation (Jeremy Gibbons and Bruno C. d. S. Oliveira, 2006).

Add up the three posts and the accounting is short. `traverse` is the one primitive: a shape-preserving walk that combines independent effects left to right. `transpose` is `traverse` with identity. The graded gadgets from [the first post](graded-gadgets.md) change what "combine" deduces, and touch nothing else. One walk; everything else is a parameter.

Conor McBride and Ross Paterson (2008). *Applicative Programming with Effects*, Journal of Functional Programming.

Jeremy Gibbons and Bruno C. d. S. Oliveira (2006). *The Essence of the Iterator Pattern*.
