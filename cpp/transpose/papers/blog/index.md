<div class="abstract" id="org44303ec">
<p>
One operation &#x2014; <code>transpose</code> &#x2014; turns out to hide a whole customization mechanism behind it.
The series starts from a loop everyone has written, names the two typeclasses underneath, shows what it costs a type to opt in and an algorithm to consume it, and ends among the prior art that kept reinventing the same idea.
Read it in order, or jump to the part you need.
</p>

</div>


# Contents

1.  [Transposing Structure and Context](transposing-structure-and-context.md) &#x2014; one operation hiding inside a loop you have written a dozen times.
2.  [Context is Applicative, Structure is Traversable](how-traverse-and-transpose-work.md) &#x2014; the two typeclasses behind the one verb.
3.  [Adapting a Type to a Typeclass](adapting-a-type-to-a-typeclass.md) &#x2014; three lines to opt in, and you never reopen anyone's class.
4.  [Writing Algorithms with Typeclass Objects](writing-algorithms-with-typeclass-objects.md) &#x2014; one algorithm, every instance, no ADL and no registry.
5.  [Prior Art: How Others Have Brought Typeclasses to C++](prior-art-typeclasses-in-cpp.md) &#x2014; FC++, `cat`, libfn, Flux, and the customization point that keeps getting reinvented.


# With running code

A second arc: the same operations demonstrated from compiled examples, with the program output captured in the posts.

6.  [Graded Gadgets](graded-gadgets.md) &#x2014; indexing fallible computation by the set of errors it can raise; `error_set`, lazy joins, and `recover`.
7.  [Transpose at Work](transpose-at-work.md) &#x2014; `transpose` run over optionals, senders, and hardware SIMD lanes, with receipts.
8.  [Traverse Does All the Work](traverse-does-all-the-work.md) &#x2014; `transpose` is `traverse` with identity, and an applicative object is the whole contract.
