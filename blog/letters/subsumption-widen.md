# Letter 3: Implicit conversion is a functor, and Lean made me say so

Steve,


# What I set out to do

You've written this conversion a hundred times without thinking about it: you have an `expected<T, error_set<parse>>`, you need to hand it to something that wants `expected<T, error_set<parse, range, io>>`, and the language just does it. The narrower error set converts to the wider one. Nobody asks it to justify itself.

I wanted to write down what that conversion actually promises. Not "it compiles": what property does it have to have for the rest of the design to be sound? The grade is a set of error kinds ordered by inclusion (call it `g \subseteq g'`), and the conversion has to behave like a **functor**: apply it at the identity relation `g \subseteq g` and get nothing changed; apply it twice, through `g \subseteq g'` and then `g' \subseteq g''`, and get the same thing as applying it once through the composite; and apply it before or after transforming the payload (mapping a function over the `ok` case) and get the same answer either way. That last one is called naturality; it's the same idea as a cast that commutes with every function you might apply to the value, rather than only some of them.

So I defined `widen`, one function taking a proof that `g \subseteq g'` and turning a `Graded g α` into a `Graded g' α`, and set out to prove the four things above.


# What the checker refused

Nothing, on the theorem I expected to fight.

The step plan flagged `widen_cast`, the interaction between `widen` (which follows a proof of set inclusion) and `cast` (which follows a proof of set **equality**, left over from the previous letter), as the likely sticking point, and told me to budget several attempts for it. I wrote the statement, reached for the obvious tactic, and it went through immediately:

```lean
theorem widen_cast (e : g = g') (h : g' ⊆ g'') (x : Graded g α) :
    widen h (cast e x) = widen (e ▸ h) x := by
  subst e; rfl
```

`subst e` replaces every occurrence of `g'` in the goal with `g` (using the equality proof `e` to eliminate the variable), which turns the two proofs of set-inclusion the theorem is juggling into proofs of the **same** inclusion up to Lean's built-in notion of sameness. `rfl` then closes the goal by definitional unfolding: once the substitution happens, both sides of the equation reduce to literally the same term, so there is nothing left to prove.

The place the checker did stop me was smaller and sillier: I attached a documentation comment to a `#guard` line (the checked, executable assertion form the project's rules require, rather than an unchecked comment), and Lean's parser rejected it, because a `#guard` isn't a named declaration and can't carry that kind of comment. An ordinary comment fixed it in one line. It cost me nothing but is worth mentioning, because it means the "friction" of formalizing subsumption was entirely administrative, not mathematical. The property really was as obvious as it feels in C++.


# What changed

I added `Graded/Widen.lean` with `widen` and five theorems: the identity law, the composition law, the naturality law, a proof-irrelevance law (any two proofs of the same inclusion widen a value identically, provable by `rfl` for the same reason as above, since propositions in Lean carry no runtime content), and `widen_cast`. I also added `fromEmpty`, which composes the previous letter's `emptyEquiv` (the isomorphism between a value at the empty grade and a bare value) with widening along "the empty set is included in everything," giving one proved function for "a plain value is acceptable wherever a graded one is expected."

In the running example, I added a third stage, `logIt`, that only ever succeeds but carries its own error grade, and a checked equality: take the parse stage's failure, widen it into the three-stage union grade, and compare that (by computation, not just by type) against the same failure built directly at that wider grade. They come out equal, which is the concrete version of "the conversion path doesn't matter."


# Back in C++

The four laws together say that subsumption is well-behaved as a **functor** (a structure-preserving map, here from the ordering on error sets to the space of possible conversions), which is exactly the informal claim built into every place you write `expected<T, error_set<...>>` and let the compiler upcast it. I went in expecting to find the fine print where that claim breaks down, the way [implicit conversions](https://en.wikipedia.org/wiki/Implicit_conversion) usually have some. I didn't find one. The theorems came out true because the representation is simple enough that there was nowhere for a counterexample to hide, which is itself worth knowing, and not something I would have been confident about without writing the proofs.

&ndash;SMD
