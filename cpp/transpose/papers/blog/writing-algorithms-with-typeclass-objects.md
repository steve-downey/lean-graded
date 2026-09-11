<div class="abstract" id="orgb92429d">
<p>
Part two showed how cheap it is to make a type an instance of a typeclass.
This is the other side of the trade: you are writing the algorithm, and you want it to run over <i>every</i> instance &#x2014; the optional, the tree, the SIMD lanes &#x2014; with the operation names reading as if they belong to your code, dispatched statically, with no ADL and no central registry.
This is where the bundled typeclass object beats traits, CPOs, and concepts alone, and why that argument is really an argument about the standard library.
</p>

</div>

**Next:** [Prior Art: How Others Have Brought Typeclasses to C++](prior-art-typeclasses-in-cpp.md) &#x2014; **Prev:** [Adapting a Type to a Typeclass](adapting-a-type-to-a-typeclass.md) &#x2014; **Up:** [Contents](index.md)


# The other chair

In part three you owned a type and wanted it to join the club. Here you own an *algorithm* &#x2014; a fold that checks a precondition, a traversal that rebuilds a structure, `transpose` itself &#x2014; and you want it to work across every type that has joined, without knowing in advance which types those are.

The typeclass object is a value: `foldable_typeclass<T>` is not a tag or a concept, it is an object you can hold and call. That single fact gives the algorithm author three ways to reach an operation, and they matter in different places.


# Three ways to reach an operation


## Implicit lookup

The common case. Look the object up by type and call operations on it.

```cpp
const auto& functor = beman::transpose::functor_typeclass<std::optional<int>>;
auto mapped = functor.fmap([](int x) { return x + 1; }, value);
```

No ADL fired. No overload set was assembled from the argument's namespace. You asked for the Functor instance of a specific type and got it.


## Explicit object argument

Pass a specific instance at the call site. Because the object is an ordinary value, you can substitute a different one &#x2014; local policy override, with no change to the type involved.

From [``examples/lookup_modes_example.cpp``](https://github.com/steve-downey/transpose/blob/blog/writing-algorithms-with-typeclass-objects/examples/lookup_modes_example.cpp):

```cpp
auto explicit_object_lookup_example() -> std::optional<int> {
    OptionalFunctorObject functor;
    std::optional<int> value{41};

    return functor.fmap([](int x) { return x + 1; }, value);
}
```

This is the thing a trait or a CPO cannot hand you: the ability to swap the *implementation* at one call site without touching, wrapping, or newtyping the value.


## NTTP pinning

Bind the looked-up object as a non-type template parameter with a default. Lookup happens once, at instantiation, and callers can override the default but do not have to.

From [``tests/beman/transpose/fold.test.cpp``](https://github.com/steve-downey/transpose/blob/blog/writing-algorithms-with-typeclass-objects/tests/beman/transpose/fold.test.cpp):

```cpp
template <class STRUCTURE,
          const auto& FOLDABLE = beman::transpose::foldable_typeclass<STRUCTURE>>
auto sum_with_nttp_lookup(const STRUCTURE& structure) {
    return FOLDABLE.fold_map([](int x) { return x; }, structure);
}
```

This is the one that matters in serious generic code. The instance is bound at instantiation, not resolved per call. It does not depend on ADL, on overload resolution, or on which namespace the call happens to sit in. If someone specializes the variable template afterward, instantiations you already made are unaffected &#x2014; the algorithm's behavior is pinned to what it saw when it was stamped out.


# Make the operations read like they are yours

Reaching an operation through a lookup object is fine for a one-liner. But when you are writing an algorithm that *composes* several operations &#x2014; check a precondition with Foldable, then rebuild with Traversable &#x2014; you do not want to qualify through a separate lookup object on every call. You want the names in scope.

So inherit from the instance. The typeclass objects are empty structs, so inheriting adds no data and slicing is a non-issue; the inheritance exists only to pull the operation names into the algorithm's own scope.

From [``examples/algorithm_object_example.cpp``](https://github.com/steve-downey/transpose/blob/blog/writing-algorithms-with-typeclass-objects/examples/algorithm_object_example.cpp):

```cpp
template <class T,
          const auto &TC = beman::transpose::traversable_typeclass<remove_cvref_t<T>>>
struct validate_impl : remove_cvref_t<decltype(TC)> {
    template <class Pred>
    auto call(Pred &&pred, const T &value) const {
        using element_type =
            typename remove_cvref_t<decltype(TC)>::element_type;
        return this->for_each(value,
            [&](const element_type &elem)
                -> std::optional<element_type> {
                if (pred(elem)) return {elem};
                return std::nullopt;
            });
    }
};
```

`for_each` is not a free function found by ADL and not a qualified call through a side object. It is an inherited member. The algorithm body reads as though `for_each` belongs to it &#x2014; and the NTTP default is doing the lookup from part three silently, once, at instantiation.


## Composing more than one machine

When an algorithm needs operations from two typeclasses, inherit from both. Both bases are empty, so there is no diamond and no storage. And the typeclass surfaces are designed with disjoint operation names, so there is no ambiguity to resolve.

```cpp
template <class T,
          const auto &FC = beman::transpose::foldable_typeclass<remove_cvref_t<T>>,
          const auto &TC = beman::transpose::traversable_typeclass<remove_cvref_t<T>>>
struct transform_if_large_impl
    : remove_cvref_t<decltype(FC)>,
      remove_cvref_t<decltype(TC)> {
    using foldable_base    = remove_cvref_t<decltype(FC)>;
    using traversable_base = remove_cvref_t<decltype(TC)>;
    using element_type     = typename traversable_base::element_type;

    template <class F>
    auto call(std::size_t min_size, F &&f, const T &value) const {
        auto n = this->foldable_base::length(value);
        if (n < min_size)
            return std::optional<T>{};

        return this->traversable_base::for_each(
            value, [&](const element_type &elem)
                       -> std::optional<element_type> {
                return {f(elem)};
            });
    }
};
```

`length` comes from Foldable, `for_each` from Traversable, and both read as members of the algorithm. Where a name is unique you write plain `this->for_each`; where two bases could both answer you disambiguate with `this->foldable_base::length`. That is the entire cost of composing two abstractions.


## Hiding all of it behind a function object

The implementation struct is plumbing. What the caller sees is one `inline constexpr` function object with a deducing `operator()` that constructs the impl, deduces the type, and gets out of the way:

```cpp
struct validate_fn {
    template <class Pred, class T>
    auto operator()(Pred &&pred, T &&value) const {
        return detail::validate_impl<remove_cvref_t<T>>{}.call(
            std::forward<Pred>(pred),
            std::forward<T>(value));
    }
};
inline constexpr validate_fn validate{};
```

```cpp
auto result = algorithm::validate(
    [](double x) { return x > 0.0; }, tree);
```

`T` is deduced. ADL is suppressed because `validate` is an object, not a function. The inheritance, the NTTP pinning, the ephemeral impl &#x2014; all invisible at the call site. The caller sees a verb.


# The naming split that makes generic code honest

There is a second thing the algorithm author gets, and it is easy to miss because it is a thing that *does not happen*.

The typeclass operation names &#x2014; `fold_map`, `traverse`, `invoke` &#x2014; are abstract, and not the names a domain expert would choose. That is correct. They name what the *concept* does, not what the *type* calls it. It is fine that they are generic to the point of blandness, because they live below the surface.

The concrete types keep their good, domain-specific names: `push_back`, `pop_min`, `insert`, `to_string`. Generic code targets that abstract layer; users targeting a concrete type get the good names.

The payoff is that you never have to lie. A design that dispatches on member names has to insist that every functor-shaped type spell its mapping operation `transform`, whether or not `transform` means anything sane for that type. Here the mapping operation is `fmap` in the adaptation layer and stays whatever it wants to be on the type's own surface. The abstraction does not colonize the vocabulary of every type it touches.


# Why not the tools we already have

Everything above is reachable, in pieces, with existing C++ facilities. The claim is not that those facilities are broken. It is that none of them, for *this* job &#x2014; a family of related operations with a small primitive core and derived defaults, over unrelated types, dispatched statically &#x2014; does what a bundled typeclass object does.


## `std::numeric_limits` &#x2014; close, but static and single-typed

The nearest standard analogy. Both are per-type specialized structs of named operations. But `numeric_limits` provides constants and `static` functions, has no derived surface, and is a *class* template &#x2014; so every specialization must instantiate the same class template. The typeclass object provides instance functions on a looked-up value, derives a large surface from a small core, and is a *variable* template, so `foldable_typeclass<vector<int>>` and `foldable_typeclass<BinaryTree<int>>` can be completely different types that merely both provide `fold_map`.


## Type traits &#x2014; predicates, not operations

`is_integral<T>` answers a question about a type. It does not hand you an operation. `foldable_typeclass<T>` does both at once: it asserts "T is Foldable" by existing, *and* it gives you `fold_map`, `length`, `to_vector`.


## CPOs &#x2014; ADL, and one operation at a time

A customization point object like `std::ranges::begin` is a single operation that finds its implementation by ADL. There is no grouping, no derivation, no object that bundles a concept's operations together. And this is the one that fails hardest on the applicative family from part two. Those operations are not independent: `map`, `zip_with`, and `apply` all derive from the `pure` + `invoke` core, and the bundle literally accepts *either* of two cores &#x2014; `invoke` or the classic `apply` &#x2014; the way Foldable takes `fold_map` or `fold_right`, deriving whichever you did not supply. A pile of one-CPO-per-operation hooks has nowhere to put that &#x2014; no shared place to derive one operation from another, or to say "either of these primitives will do." That is the coherence a bundle keeps and à la carte CPOs throw away. `std::simd::vec` is the registered proof: it supplies `pure` and `invoke`, `apply` cannot be derived for it (no `vec<callable>` exists to hold a function), and every derived operation still works. Under a lone global `apply` CPO that type is simply locked out; under the bundle it participates.


## Concepts &#x2014; constraints, not dispatch

C++20 `concept` s constrain a template; they do not dispatch to an implementation. `foldable_typeclass<T>.fold_map(f, value)` finds and calls the right code for `T`. Worth saying plainly: C++0x Concepts had `concept_map` s meant for exactly this role, and they were lost in the move to Concepts Lite. The variable-template approach is a library-level recovery of that idea. (Bjarne Stroustrup, 2009)


## Rust traits &#x2014; the closest relative

A Rust trait bundles operations with default implementations, types `impl` it explicitly, and the compiler dispatches statically by monomorphization. That is nearly a description of this pattern. The difference is that here dispatch is *explicit* &#x2014; you call through the looked-up object &#x2014; rather than resolved by the compiler from a trait bound. Slightly more syntax; in exchange, the call-site override from earlier, which a trait bound does not offer.


# Where it matters, and why it belongs in the standard

This is not a demonstration written once against one type. In this proposal's own repository the same fold and traversal algorithms run, unchanged, over a `BinaryTree<T>` ([``examples/binary_tree.hpp``](https://github.com/steve-downey/transpose/blob/blog/writing-algorithms-with-typeclass-objects/examples/binary_tree.hpp)) *and* over the contextual types from part one &#x2014; `optional`, `std::execution` senders, and lanewise ~zip\_list~/SIMD &#x2014; which share nothing with a tree and nothing with each other, yet enter through the identical mechanism.

The same `foldable_typeclass` / `traversable_typeclass` machinery reaches further in the coordinated paper set, over structures this paper deliberately leaves to its companions:

-   a persistent, concatenable *measured sequence* of finger-tree lineage (Ralf Hinze and Ross Paterson, 2006) &#x2014; the subject of the companion persistent-sequence paper (Paper C)
-   a recursive fixpoint tree `Fix<F>` &#x2014; the subject of the companion recursive-tree-algorithms paper (Paper D)

Those belong to separate papers on purpose: this one standardizes the traversal/transposition entry point and the customization mechanism behind it, not a menagerie of containers. What matters here is that a *single* adaptation mechanism already spans a flat container, a balanced tree, a persistent sequence, a recursive fixpoint, and three computational contexts &#x2014; each instance in its own header, none of them knowing about the others.

The type definitions do not know about the typeclasses. The typeclasses do not know about each other. The call site does not change when the representation changes. Independent extension points that compose &#x2014; no reopening classes, no monkey-patching, no registry.

Which is the real argument of this series. `transpose` is one operation the standard library has no spelling for, and consuming it &#x2014; writing the algorithms &#x2014; is where a *bundle* beats every à la carte alternative, because the applicative family only holds together when its operations derive from a small coherent core rather than being scattered across independent hooks.

Standardizing `transpose` and `traverse` without standardizing something like this substrate would push the customization story back toward trait-only or `tag_invoke`-heavy designs &#x2014; exactly the designs that fracture the family, scattering `pure`, `invoke`, `apply`, `map`, and `zip_with` across independent hooks with no shared place to derive one from another. The verbs need a mechanism strong enough to keep their primitive and derived operations coherent across unrelated types. That is what a typeclass object is.

And it degrades gracefully. If C++ later grows richer generic facilities &#x2014; pattern matching, a real return of concept maps &#x2014; this API should get *simpler*. It should not need to be replaced. That is the mark of proposing the right shape rather than a workaround: the workaround gets thrown away when the language catches up; the right shape just gets a better implementation underneath.

That leaves one question the series has not yet answered: if the shape is right, why has no one standardized it &#x2014; and what has everyone built instead? That is part five, [Prior Art: How Others Have Brought Typeclasses to C++](prior-art-typeclasses-in-cpp.md).

Bjarne Stroustrup (2009). *The C++0x \`\`Remove Concepts'' Decision*.

Ralf Hinze and Ross Paterson (2006). *Finger Trees: A Simple General-Purpose Data Structure*, Journal of Functional Programming.
