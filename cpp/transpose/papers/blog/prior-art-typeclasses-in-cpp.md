<div class="abstract" id="org3189422">
<p>
The variable-template concept map from parts two and three was not invented in a vacuum.
Bringing functional and typeclass-style programming to C++ is a decades-old sport, and every serious attempt makes a real trade.
This closing part places the pattern among its neighbours &#x2014; an ancestor from before C++ had lambdas, a whole category-theory hierarchy, a library that extends the standard vocabulary types, and a safe-iteration model on a different axis &#x2014; and asks what it is that keeps getting reinvented.
</p>

</div>

**Prev:** [Writing Algorithms with Typeclass Objects](writing-algorithms-with-typeclass-objects.md) &#x2014; **Up:** [Contents](index.md)


# Not invented in a vacuum

Parts two and three argued for a single pattern: a variable template used as a concept map, a looked-up *dictionary* of a concept's operations, bundled, statically dispatched, attachable to types you do not own. Making that case without showing the neighbours would be a cheat. People have been bringing functional and typeclass-style programming to C++ for twenty-five years, and each attempt is the right answer to a slightly different question.

What follows is four of them, plus the one the standard itself tried and dropped. I checked every claim here against the primary sources, not the summaries around them; where the popular retelling overstates, I say so, because a fair comparison is the only kind worth making.


# FC++: the ancestor, before the language helped

Two decades ago &#x2014; before C++ had lambdas, before `auto` &#x2014; Brian McNamara and Yannis Smaragdakis built FC++ (Brian McNamara and Yannis Smaragdakis, 2000), a pure-functional layer that required no changes to the compiler or the language at all.

Its unit is the *functoid*: a function-object class carrying a nested `Sig` member template that computes its own return type. On that foundation FC++ delivered genuinely higher-order polymorphic functions, automatic currying (call a function with some of its arguments and get back a function awaiting the rest), a subtyping rule for functions themselves (covariant in the result, contravariant in the arguments), lazy and infinite lists, and more than fifty functions lifted straight from the Haskell Prelude.

Be precise about the cost, because the folklore overstates it. The paper concedes that a type error "reports the full template instantiation stack," but it calls its own error reporting "adequate"; and the famous order-of-magnitude speed-up was a gain over FC++'s *own earlier* version on lazy-list-heavy benchmarks, not an absolute claim that functional C++ runs ten times faster than anything. The real lesson of FC++ is not that it was slow or ugly. It is that all of this was reachable in C++ *before the language offered any help* &#x2014; and that reaching it took heroic machinery: the `Sig` return-type protocol, hand-built curryable combinators, reference-counted list cells. Much of the language evolution since has been, in effect, a project to make it unnecessary.


# awgn/cat: the whole hierarchy, on traits

If FC++ is the ancestor, Nicola Bonelli's [`cat`](https://github.com/awgn/cat) is the maximalist. It is a C++20 library that ports the category-theory hierarchy more or less wholesale &#x2014; Functor, Bifunctor, Applicative, Alternative, Monoid, Monad, MonadPlus, Foldable, Show, Read &#x2014; with no macros, confining the metaprogramming to a set of type traits (`is_container`, `function_arity`, `return_type`, and their kin), and adding callable wrappers so that composition and currying work over any callable, `std::bind` expressions and generic lambdas included.

`cat` is the closest relative in spirit to the pattern in this series: it too adapts standard types *from the outside*, by specializing traits rather than by touching the types. The differences are of shape and ambition. `cat` is a whole framework you adopt &#x2014; the full hierarchy, its trait vocabulary, its wrappers &#x2014; where the variable-template map is a small technique you can apply to exactly one concept. And `cat`'s adaptation surface is a set of *traits*: compile-time predicates and type functions. The map's surface is a first-class *value* &#x2014; a dictionary object you can look up, pin as a template parameter, or substitute at the call site. One is a library to buy into; the other is a pattern to reach for. In fairness, `cat` is also a single-author project last updated in early 2023: evidence that the idea works, not infrastructure to build on.


# libfn: extend the standard types themselves

[`libfn`](https://github.com/libfn/functional) (the `fn::` library) asks a different and very practical question. Not "how do we build a hierarchy," but "how do we make the standard vocabulary types *themselves* better at functional composition, in a way the committee might one day adopt?"

Its answer is direct: it extends the std types *by inheriting from them*. `fn::optional` publicly derives from `std::optional`, marked `final` and adding no data members; `fn::expected` presents the same monadic surface over an `expected`-shaped base. This gets waved off as dangerous, but the usual hazard &#x2014; *slicing* &#x2014; only ever removes *data*, and here there is no data to remove. You cannot slice off an API in any meaningful sense: copy an `fn::optional` into a `std::optional` and nothing of value is lost, because the extension was interface, not state. A `final`, zero-storage, member-function-only derivation is simply a richer interface bolted onto an existing type &#x2014; a perfectly reasonable way to extend one. On top of that it builds type-indexed sum types (coproducts), a tuple-like `pack` product, a `choice` monad dispatched by overload-resolution rules, and *graded monads* that let an `expected`'s error type grow and change along the pipeline. It is aimed squarely at standardization: it targets GCC 13 and Clang 18, leans on a proposed C++26 type-ordering facility, and keeps a deliberately unstable contract in which every minor version is a breaking change.

The contrast with out-of-band adaptation is still real, and it is not about safety. The thing you get is a *new type*, `fn::optional`; your existing `std::optional` values do not acquire the new operations. Out-of-band adaptation is the opposite bet: leave `std::optional` exactly as it is, in `std`, untouched, and attach the operations from the outside. Both are legitimate, and they answer different questions. libfn wants *better standard types*. The concept map wants to teach the *existing* ones new tricks without owning them &#x2014; which is the only option at all when the type is a third party's sender or a hardware SIMD register you cannot subclass into anything useful.


# Flux: a different axis entirely

[`Flux`](https://github.com/tcbrindle/flux) belongs in this survey precisely because it is *not* a customization mechanism. Tristan Brindle's Flux is a C++20 sequence library that replaces STL iterators with *cursors*. Where an iterator generalizes a pointer and knows how to advance itself, a Flux cursor generalizes an *index* and knows nothing: every operation &#x2014; `first`, `is_last`, `inc`, `read_at` &#x2014; takes the sequence and the cursor together. Because the sequence is always in hand, bounds checking is cheap and universal, one cursor type serves both const and mutable access, and a dangling cursor is impossible by construction. (Flux is careful about what it promises here: it does *not* claim cursors survive reallocation, only that a stale position is caught by the next bounds check rather than reading freed memory.)

Why include it at all? Because `traverse` and `transpose` from part one are *internal-iteration* operations, and Flux is what a safe internal-iteration substrate looks like. It is a neighbour, not a rival. Flux answers "how do we iterate without dangling"; the concept map answers "how do we adapt a type to a concept." Those are orthogonal, and they compose &#x2014; you could imagine the traversal verbs riding on a cursor-safe sequence instead of raw iterators.


# The one the standard already lost

The most important prior art is in the standard itself. C++0x &#x2014; the draft that became C++11 &#x2014; was slated to include *concept maps*: a way to associate a concept's operations with a type *out of band*, so that a `student_record` with no `operator==` could be made `EqualityComparable` without editing `student_record` (Bjarne Stroustrup, 2009). Concept maps were dropped in the retreat to "concepts lite," and the C++20 concepts we got test whether an expression compiles; they carry no implementations. The customization job concept maps would have done fell instead to customization point objects and `tag_invoke` &#x2014; today's answer, and one still bound to argument-dependent lookup, with all the namespace sensitivity that implies. (Part three walks through why that does not hold an applicative family together.)

The variable-template concept map is, almost literally, a library-level recovery of the feature the standard lost. The dictionary object *is* the concept map: looked up by type, holding the operations, specializable for a type its author never anticipated.


# Why not just use Haskell, or Rust?

None of this is a claim to originality about the *theory*. Typeclasses, applicatives, traversable structures, monoids &#x2014; Haskell, Scala, and PureScript worked these out long ago, and I borrow and steal from them without apology. Sound theory is sound; there is nothing to gain by reinventing it. The dictionary that the variable-template map looks up is not even a novel encoding: it is, deliberately, how the Glasgow Haskell Compiler *implements* typeclasses underneath &#x2014; a class becomes a record of functions, handed to the polymorphic code that needs it (Philip Wadler and Stephen Blott, 1989). Rust does the same job by monomorphization: a trait is a bundle of operations with defaults, types `impl` it explicitly, and the compiler dispatches statically. A Rust trait is the closest language-level relative this pattern has, and the resemblance is no accident &#x2014; it is the same idea, with the compiler rather than the programmer holding the dictionary.

So why not simply write the code in one of those languages and be done? Because the problem was never to find a language with sound abstractions. It is that the code that needs them is *already in C++*: the `std::optional` you are handed, the `std::execution` senders, the SIMD registers, the containers, the ABI you must not break, the libraries and teams and years of investment that will not be rewritten in Haskell to gain a `traverse`. The whole task is to bring the sound theory *into* C++ &#x2014; with tools that are themselves sound: static, zero-overhead, non-intrusive, honest about what they cost &#x2014; rather than to emigrate to a language that already has it. That is what every library in this survey is doing, mine included: porting a settled idea into the language where the work actually lives.


# Where the pattern sits &#x2014; and what it costs

Line the attempts up and the niche is obvious.

-   FC++ proved functional C++ was possible before the language helped, at the cost of heroic machinery.
-   `cat` builds the entire hierarchy out of band, as a framework to adopt.
-   libfn improves the standard types themselves, by deriving new types from them.
-   Flux makes iteration safe, on a different axis.

The variable-template concept map takes a narrower bet than any of them: adapt a type you *cannot touch* &#x2014; `std::optional`, a third-party sender, a hardware SIMD register &#x2014; to a *bundle* of operations, from the outside, with static dispatch, no ADL, no inheritance, and no reopening; and let generic algorithms look that bundle up as a value.

The honest cost is the one parts two and three already named: you call the operations *through* the looked-up object, not as free functions or member syntax. It is more explicit &#x2014; more verbose &#x2014; than a CPO or an overloaded operator. That verbosity is the price of the properties, and it is a price worth stating, not hiding. What it buys is a customization surface that is a value you can name, pin, and swap, over types whose authors will never know your concept exists.


# Why the recurrence is the argument

Step back from the particulars and the striking thing is the *repetition*. FC++ hand-rolled higher-order dispatch in 2000. `cat` rebuilt the hierarchy on traits in 2023. libfn is re-deriving it from the standard types right now. Senders and receivers encode the same monadic structure yet again, inside P2300. Every few years someone re-implements out-of-band customization and the operations that ride on it, because the language still has no single agreed way to say "this type satisfies this concept, and here is how."

That recurrence *is* the standardization argument, in one sentence. The demand is real, it is durable, and it keeps being met privately and incompatibly. Concept maps were the standard's own answer, and the standard dropped them. A small, bundled, out-of-band customization mechanism &#x2014; whatever its eventual spelling &#x2014; would let all of this stop being reinvented. The pattern in this series is one concrete, working proposal for that mechanism. It is not the only one possible. But four independent attempts in twenty-five years, all circling the same missing feature, tell you the hole is there.

Bjarne Stroustrup (2009). *The C++0x \`\`Remove Concepts'' Decision*.

Brian McNamara and Yannis Smaragdakis (2000). *Functional Programming in C++*.

Philip Wadler and Stephen Blott (1989). *How to Make Ad-Hoc Polymorphism Less Ad Hoc*.
