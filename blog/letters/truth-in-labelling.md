# Letter 23: The three sentences nothing was checking

Steve,


# What I set out to do

I went back over the whole model looking for places where it claimed more than it had proved, and found three. The job was to fix the sentences and nothing else: no new definition, no new theorem, no change to anything Lean checks. That turned out to be a more interesting afternoon than it sounds like.

The traverse module said that `foldGrade_cons_ne_nil` established "the precision claim, that grade `g` is not padding, that no error kind admitted by the signature is actually unreachable". What the theorem says is that folding `g` over a nonempty list gives back `g`. Those are different sentences. A function that always succeeds can be typed as returning `Graded {parse} Nat`, and the fold theorem holds of it word for word, with `parse` something that function will never produce.

The canonicalization module opened `canonEquiv` with "The Lean statement of \`error\_set<A,B>\` and \`error\_set<B,A>\` are the same type". It is a bijection between a `Finset` and a sorted list. Both of those are Lean spellings of one grade. Neither one is a C++ type, and nothing in the file goes near an alias, a mangled name, or a second translation unit.

And `Pomonoid` is documented as a partially ordered monoid. Its order fields are reflexivity and transitivity. There is no antisymmetry field. It is a preorder, and it has been a preorder since the day it was written.


# What the checker refused

Nothing. That's the finding, and it's why this letter exists.

All three claims live in docstrings and in the design document, and Lean has no opinion about either. The build was green before I started and green when I finished, and it would have stayed green if I had written the opposite of each sentence instead. The one part of this repository that states things without proving them is the part with no checker on it, and that is where all three of these were sitting.

The `Pomonoid` one deserves a second look. The design document already contained the correct statement. Buried in a note about how strong a grade's join has to be, six hundred lines away from the class it describes, is the line "`Pomonoid` simply does not require it as a field, so `le` there is really a preorder". So the document knew. One paragraph said preorder, another said partial order, and they sat there together across two steps, because nothing in the build reads either one.

I would rather have found this by having a proof fail.


# What changed

Prose, and only prose. 203 theorems before, 203 after, and the generated law inventory came back byte for byte identical, which is how I know I did what I said I was going to do.

The traverse docstring now says what `foldGrade_cons_ne_nil` actually is: an annotation-normalization fact. A nonempty traversal's stated grade is `g` on the nose, the same `g` the element function already carries, so the length of the list never leaks into the type. Under it there is a paragraph headed with what the theorem does not say, and the always-succeeds example is in it.

`canonEquiv` is now labelled a representation theorem, followed by the list of things it is not: alias identity, evidence about any particular metaprogram, mangling stability, agreement between translation units. Those all belong to `static_assert`. The division I wrote down is that Lean owns the normal-form arithmetic and C++ owns type identity.

`Pomonoid` keeps its fields and, for now, its name. Adding antisymmetry would charge every monad, applicative, traversal and morphism law in the model for a property none of their proofs uses, which is the thing this project exists to avoid doing. And renaming it today buys less than it appears to: the two grades in the tree are `Finset` under inclusion and `Nat` under `≤`, both antisymmetric, so a class separating preorder from partial order would be a class both of them satisfy. I want a grade that fails it first, and there is an obvious candidate waiting, the raw unsorted pack, where `[A,A]` and `[A]` are each below the other and are still not equal.

I didn't touch the earlier letters. They are dated accounts of what I understood that week, and one of them is called `grade-pomonoid`. Editing them to match what I know now would be a worse dishonesty than the one I was fixing.


# Back in C++

The reachability one is what to carry back. If you write

```c++
expected<vector<int>, error_set<parse_error, range_error>> parse_all(...);
```

the error set is an upper bound your signature declares. It promises that nothing else comes out, and that direction is proved: an error that appears was admitted by the set. It doesn't promise that both of those can happen. A version whose range check can never fire has the same type, compiles the same, and nothing will tell you the second alternative is dead. Whether every listed error is reachable is a property of your code, it is usually false in some corner of a large one, and it isn't something the type system is trying to say.

A grade that is too wide is legal, silent and free. That is the right default. But it does mean that "the error set documents what can go wrong" is a claim about your discipline. The type doesn't say it, and I had been writing it down as though the model had established it.

For canonicalization the boundary is cleaner. What makes `error_set<A,B>` and `error_set<B,A>` one type is the alias and the sorted carrier behind it, and what checks it is a `static_assert` you have to write and run. What I have proved is that a sorted normal form cannot tell those two spellings apart. That is the arithmetic your metaprogram has to get right. It is not evidence that it does.

&ndash;SMD
