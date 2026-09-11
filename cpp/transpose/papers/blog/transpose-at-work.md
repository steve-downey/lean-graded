**DRAFT &#x2014; pending author revision**

<div class="abstract" id="orge842495">
<p>
<a href="transposing-structure-and-context.html">The opening post of this series</a> argued that <code>vector&lt;optional&lt;T&gt;&gt;</code> to <code>optional&lt;vector&lt;T&gt;&gt;</code> is one operation, <code>transpose</code>, and that the same verb covers deferred and lanewise computation.
This post runs it.
The code is transcluded from a compiled example in the <a href="https://github.com/bemanproject/transpose"><code>beman.transpose</code></a> repository and the output is captured from the built binary: absence hoisted out of a vector, a composed sender that provably doesn't run until asked, and hardware SIMD lanes transposed through <code>std::simd</code> on GCC 16.
</p>

</div>

**Prev:** [Graded Gadgets](graded-gadgets.md) &#x2014; **Next:** [Traverse Does All the Work](traverse-does-all-the-work.md) &#x2014; **Up:** [Contents](index.md)


# The loop, gone

The problem from the first post: all of the values if every element is present, nothing if any element is missing. Here it is as a call, once with no gaps and once with one.

```cpp
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
```

    complete input:  has_value = true
    gapped input:    has_value = false
    transposed:      [1, 2, 3]

No reserve, no early exit, no accumulate. The declaration `std::optional<std::vector<int>>` on the left is doing the documentation too.


# Deferral survives the composition

A `sender` here is the library's minimal stand-in for a P2300 sender: a lazy value that runs when you call `get()`. The interesting property is what `transpose` must *not* do: composing a vector of senders into one sender of a vector had better not run anything.

To make the laziness visible, each sender announces itself when it actually executes.

```cpp
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
```

    composed vector<sender<int>> into sender<vector<int>>; nothing has run yet
      running the sender for 3
      running the sender for 2
      running the sender for 1
    after get():
      [1, 4, 9]

Read the output in order. The "nothing has run yet" line prints *before* any sender announces itself; nothing executes until `get()`. And then GCC happens to run the three computations right to left, because they sit as arguments to one deferred call and argument evaluation order is the compiler's to choose. The computations are independent, so no order was promised; the values still land in position order, `[1, 4, 9]`. The transposition rearranged types, not execution.


# Lanes

The lanewise context is `simd_lanes<T, N>`: an `N`-lane array, filled here from real `std::simd::vec` registers (P1928, in GCC 16). Three positions of four lanes each transpose into four complete result vectors, one per hardware lane.

```cpp
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
```

    3 positions x 4 lanes -> 4 lanes of vector<int>
      lane 0: [1, 10, 100]
      lane 1: [2, 20, 200]
      lane 2: [3, 30, 300]
      lane 3: [4, 40, 400]

Lane 0 holds the first element of each position's computation, lane 1 the second, and so on. It's the same data-layout flip as the `optional` case; only the meaning of the context changed.


# Three contexts, one specification

Nothing about `transpose` was overloaded per domain. The structure (`vector`) knows how to be walked and rebuilt; each element context (`optional`, `sender`, `simd_lanes`) knows how to combine independent computations; `transpose` is the fixed rule connecting the two. The per-context knowledge lives in two lookup objects, `traversable_typeclass` for the structure and `applicative_typeclass` for the context, as [the adaptation post](adapting-a-type-to-a-typeclass.md) described.

Which leaves the actual mechanism unexplained. The umbrella header states it in one comment: `transpose` is `traverse` with the identity function. That single sentence, from McBride and Paterson's distributive law (Conor McBride and Ross Paterson, 2008), is the entire implementation, and unpacking it is the next post.

Conor McBride and Ross Paterson (2008). *Applicative Programming with Effects*, Journal of Functional Programming.
