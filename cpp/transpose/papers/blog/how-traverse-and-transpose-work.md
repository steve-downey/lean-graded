<div class="abstract" id="org0af3a19">
<p>
Part one flipped <code>structure&lt;context&lt;T&gt;&gt;</code> into <code>context&lt;structure&lt;T&gt;&gt;</code> with one verb, <code>transpose</code>, across three contexts that share nothing &#x2014; and left the machinery unopened.
This part opens it, and there is less inside than the names suggest.
The two axes each have a job and a name: the <i>structure</i> is <b>Traversable</b>, the <i>context</i> is <b>Applicative</b>, and <code>traverse</code> and <code>transpose</code> are built from exactly those two.
No prior category theory required &#x2014; that is rather the point.
</p>

</div>

**Next:** [Adapting a Type to a Typeclass](adapting-a-type-to-a-typeclass.md) &#x2014; **Prev:** [Transposing Structure and Context](transposing-structure-and-context.md) &#x2014; **Up:** [Contents](index.md)


# Two axes, two jobs

Everything in part one had the shape `structure<context<T>>`: a `vector` of `optional`, a `vector` of senders, a `vector` of SIMD lanes. Two things are stacked there, and they do different work.

-   The *structure* &#x2014; the `vector`, or a tree &#x2014; is a shape you can *walk* and *rebuild*. That capability has a name: **Traversable**.
-   The *context* &#x2014; `optional`, a sender, a lane array &#x2014; is a value sitting in some setting, and the setting can be *combined* across independent positions. That capability has a name too: **Applicative**.

Name those two and the rest follows mechanically. `traverse` walks a Traversable while collecting results in an Applicative; `transpose` is the special case where there is nothing to collect but the contexts themselves. This whole post is those two ideas and how they click together.


# Context = Applicative

A *context* is a value in a setting. `optional<T>` is a `T` that might be absent. A sender of `T` is a `T` that has not been computed yet. A `simd_lanes<T, N>` is `N` values of `T`, one per lane.

To be an **Applicative**, a context needs exactly two operations.


## `pure`: the trivial way in

`pure` takes a plain value and drops it into the context in the most boring way possible.

```text
pure : T -> C<T>
```

For `optional`, `pure(x)` is `Some(x)`. For a sender, it is a sender that immediately yields `x`. For `simd_lanes`, it is `x` broadcast to every lane. Nothing interesting happens; that is what makes it the *identity* for building bigger things.


## `invoke`: combine independent things in context

`invoke` is the one with content. Given a *plain* function and arguments that each sit *inside the context*, it produces the result *inside the context*.

```text
invoke : (T... -> U), C<T>... -> C<U>
```

Read it as: the context knows how to combine several in-context values under one ordinary function. Concretely, three ways:

-   `optional`: if every argument is present, call the function and wrap; if any is absent, the result is absent.
-   sender: a new sender that, when run, runs all the operands and then calls the function.
-   `simd_lanes`: call the function lane by lane, producing a lane array of results.

That is the entire obligation. Give a context `pure` and `invoke` and it is an Applicative.


## The everyday verbs are derived

You get a friendlier surface for free, because everything else falls out of `pure` + `invoke`:

-   `map(f, cx)` is just `invoke` with one argument.
-   `zip_with(f, cx, cy)` is `invoke` with two.
-   `apply(cf, cx)` &#x2014; the textbook primitive, a function *already inside the context* applied to an argument inside the context, `C<(T -> U)>, C<T> -> C<U>` &#x2014; is `invoke` of "evaluate": `invoke([](f, x){ return f(x); }, cf, cx)`.

That last line deserves a pause, because the classic literature runs it the other way around &#x2014; `apply` as the primitive, everything derived from it. Both presentations are equivalent when the context can hold a function, and a type may supply whichever core is natural (part three shows how). But `invoke` is the more *general* shape: it never needs a function to sit inside the context at all. Some contexts &#x2014; a hardware SIMD register is the concrete one &#x2014; can hold numbers but not callables, so `apply` for them cannot even be spelled, while `invoke` is perfectly well-defined. That is why `invoke` is the core here, and `apply` the derived convenience that exists where it can.


# Independence is the whole point

Here is the property that makes it **Applicative** and not something stronger.

In `invoke` &#x2014; and so in `map`, `zip_with`, and the classic `apply` &#x2014; the arguments are *independent*. Combining two in-context values never lets one value *steer* the other's computation. An `optional`'s presence does not depend on another `optional`'s contents. One sender does not wait to see another's result before starting. One SIMD lane does not consult its neighbour.

That independence is not a limitation to apologize for; it is the source of the power. Because the pieces do not depend on each other, their *shape* is fixed in advance and their *effects* simply combine, left to right. That is exactly what lets an operation preserve structure and merge contexts in one pass.

Contrast the stronger thing, a **Monad**, whose primitive is `bind`: *feed one result into the choice of the next computation*. `bind` is sequencing &#x2014; each step may depend on the value the previous step produced. That is a real and useful capability, and the standard library already serves it well (monadic `optional`, sender adaptors, coroutines). It is simply a *different* operation, and the traversal story does not need it. Applicative is the weaker, more widely available power, and weaker is what makes it universal.


# Structure = Traversable

Now the other axis. A structure is **Traversable** if it can `traverse`: visit each element, turn it into a context, and reassemble &#x2014; with the shape preserved &#x2014; into one context wrapping the whole structure.

```text
traverse : (T -> C<U>), structure<T> -> C<structure<U>>
                        requires: structure Traversable, C Applicative
```

Give `traverse` a function `f : T -> C<U>` and a `structure<T>`, and it produces a `C<structure<U>>`: the same shape, one context on the outside.

Mechanically it is a fold that threads `pure` and `invoke`:

-   start from `pure(empty)` &#x2014; the empty rebuilt shape, already in the context;
-   for each element, `invoke` a "grow the structure by one" step over *two* in-context values: the structure accumulated so far, and `f` applied to this element;
-   finish with a context holding the fully rebuilt structure.

Every step uses the context's Applicative to combine, and the structure's own knowledge to walk and rebuild. That is why `traverse` needs *both* typeclasses at once: Traversable to visit and reconstruct, Applicative to combine what the visits produce.

A concrete case. Take `f : int -> optional<int>` &#x2014; say, parse-or-fail. Then `traverse(f, vector<int>)` is an `optional<vector<int>>`: every element parsed, or nothing if any failed &#x2014; the fallible loop from part one, now a one-liner, with the shape preserved on success.


# transpose = traverse with identity

`transpose` is the case you have already seen, and it is just `traverse` with nothing to do per element.

When the structure is *already* `structure<context<T>>` &#x2014; each element already a context &#x2014; there is no function left to apply; you only need to combine the contexts that are sitting there. That is `traverse` with the identity function:

```text
transpose(structure<context<T>>)  =  traverse(identity, structure<context<T>>)
                                   =  context<structure<T>>
```

Everything true of `traverse` is true of `transpose`: it needs the structure Traversable and the context Applicative, it preserves shape, it combines effects left to right, and it rests on independence. This is precisely why part one's single `transpose` verb worked, unchanged, over `vector<optional>`, `vector<sender>`, and `vector<simd_lanes>`: each inner type is an Applicative context, `vector` is Traversable, and `transpose` is `traverse` of the identity.


# Two capabilities, genuinely two

It is fair to ask whether Traversable and Applicative are really different things, since the familiar examples &#x2014; `vector`, `optional`, `zip_list` &#x2014; tend to have both. They are, and the reference implementation carries the proof.

`std::simd::vec` (C++26, real since GCC 16) is a registered Applicative in this library: `pure` broadcasts a scalar to every lane of a hardware register, `invoke` applies a plain function lane by lane. But it is *not* Traversable, and cannot be: a SIMD register holds vectorizable scalars only, so `vec<vector<T>>` is not a type &#x2014; there is no "vec of structures" to rebuild into, and nothing for `transpose` to produce. It combines like a context; it cannot be walked and reassembled like a structure. (The same restriction is why it is the invoke-only applicative: `vec<callable>` is not a type either.)

This is the same situation as Functor and Foldable: every Foldable worth the name is a Functor, but not every Functor is Foldable &#x2014; a function `R -> T`, read as a context of `T` s indexed by `R`, maps perfectly well and cannot be folded. Overlap is common; identity is false. The lanewise context that *does* go through `transpose` is `simd_lanes` &#x2014; an ordinary array of lanes, Applicative and Traversable both &#x2014; with `std::simd::vec` doing the hardware arithmetic that fills it.


# The whole map, in one place

```text
   structure< context<T> >   -- transpose -->   context< structure<T> >

   structure   = the OUTER type   = Traversable   ( traverse: walk + rebuild )
   context     = the INNER type   = Applicative   ( pure + invoke: combine, independently )

   traverse   : (T -> C<U>), structure<T> -> C<structure<U>>   -- needs one of each
   transpose  : structure<C<T>> -> C<structure<T>>             -- = traverse identity
```

That is the entire theory the series needs. Two typeclasses &#x2014; one for the shape you walk, one for the effect you combine &#x2014; a single operation, `traverse`, built from the pair, and `transpose` as its identity case. In the code these are the objects `traversable_typeclass<Structure>` and `applicative_typeclass<Context>`; the next three parts are, in order, how a type *becomes* one of them, how you *write algorithms* against them, and who has built this before.


# Further reading, not prerequisites

The idea that *independent* effects deserve their own weaker-than-monad structure is Conor McBride and Ross Paterson's **Applicative Programming with Effects** (Conor McBride and Ross Paterson, 2008). The idea that traversal is the essence of walking a structure while collecting an effect is Jeremy Gibbons and Bruno Oliveira's **The Essence of the Iterator Pattern** (Jeremy Gibbons and Bruno C. d. S. Oliveira, 2006). Both are worth reading &#x2014; but you did not need either to get here, and that is the whole design goal: the machinery is small enough to hold in your head with two names and one operation.

Next, part three, [Adapting a Type to a Typeclass](adapting-a-type-to-a-typeclass.md): what it takes to make *your* type one of these &#x2014; to write its Applicative or Traversable instance &#x2014; which turns out to be about three lines.

Conor McBride and Ross Paterson (2008). *Applicative Programming with Effects*, Journal of Functional Programming.

Jeremy Gibbons and Bruno C. d. S. Oliveira (2006). *The Essence of the Iterator Pattern*.
