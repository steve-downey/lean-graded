# Letter 19: error\_set has to be a semilattice because of what it promises, not what it does

Steve,


# What I set out to do

Letter 14 answered "what does a grade have to be" with three layers, nested: a pomonoid carries `and_then=/=apply=/=traverse`, commutativity adds order-independence, idempotence adds length-independence. Each layer looked like it bought more grade. Letter 18 then produced a fact that account can't explain on its own: `apK_flip`, the cast-free twin of `ap_flip`, needs no property at all, where `ap_flip` needs `Grade.join_comm` by construction. So this letter's question was: is commutativity really "more grade", or was it only ever the cost of writing the result grade as an exact union? And if that's true of commutativity, is it true of idempotence too?

The way to answer it honestly was to stop guessing and read every proof that cites either property, one at a time, and ask what it's actually doing: computing a value, or reconciling two ways of writing the same grade.


# What the checker refused

Nothing, this time, in the sense of a red build. What the **evidence** refused was my own first pass at the classification. I went in expecting `Comp.traverseComp_cons` and the `traverse_cons` family to be an easy "yes, canonicalization, next" - they cite idempotence, they cast, done. But "cites idempotence" and "needs it to pick a value" are different claims, and I'd conflated them. So I actually traced the tactic proof of each one, case split by case split. `traverse_cons`'s proof is: look at `f x`, look at the recursive traversal's shape, and once both are pinned to `ok` or `err`, close with `cast_ok=/=cast_err`. The idempotence lemma never appears inside that case split. It only appears in the **type** of the cast being closed - identifying the folded grade `g ⊔ g` with `g`. The value was already decided before idempotence entered the picture at all. Same story, one layer up, for `Comp.traverseComp_cons`.

The one row that didn't resolve cleanly was `foldG_le`, the generic version of "the traversal grade never exceeds `g`." Its concrete sibling, `foldGrade_le`, is genuinely part of **defining** `traverse`, and needs only order, no idempotence - so "bounded by `g`" sounded like an operational fact. But the generic `foldG_le` needs idempotence, and I had to work out why before I could write that row down honestly.


# What changed

The classification, checked theorem by theorem against the generated table (`docs/laws.md`, not any earlier letter's prose - two of them disagreed with their own tables at least once), comes out clean: every single citation of `join_comm` or `join_idem` in the model is a claim that two expressions denote the same grade, or that a grade equals some fold. None of them is a claim about what `bind`, `ap`, `traverse`, `widen`, or `rename` computes for a real payload or a real error. `ap_flip` and `flatten_comm` are both a `cast (Grade.join_comm ...)` reconciling two orderings of a union. `joinAll_perm` and `join_mem_eq` are pure grade arithmetic with no carrier value in sight at all. And the traversal family, once traced, turned out to be exactly what I'd hoped it wasn't and had to check anyway: cast-target reconciliation, never value selection.

`foldG_le` turned out to be neither a counterexample nor a clean confirmation - it's a fact about the grade's own bookkeeping, not about a carrier value, and its need for idempotence is an artifact of one choice: `Graded/Obligations.lean` deliberately doesn't make "join is a least upper bound" a primitive fact, because doing so would stop `Nat` (my non-idempotent counter-instance) from being a pomonoid at all. Take that choice away and boundedness only comes back through idempotence. At `Grade` itself, though, boundedness is free - `Finset` union already is a lattice join. The generic dependency is a fact about how the **abstraction** was built, not about what any traversal needs from a value.

With the hypothesis holding, I restructured the three-class tower into one operational class and three siblings:

```lean
class Pomonoid (G : Type u) where           -- unchanged: the operational obligation
  join, bot, le, join_assoc, bot_join, join_bot, le_refl', le_trans', bot_le, join_mono

class IsCommPomonoid (G : Type u) extends Pomonoid G where
  join_comm : ∀ a b, join a b = join b a

class IsIdemPomonoid (G : Type u) extends Pomonoid G where   -- no longer needs IsCommPomonoid
  join_idem : ∀ a, join a a = a

class IsCanonicalPomonoid (G : Type u) extends Pomonoid G where
  join_comm : ∀ a b, join a b = join b a
  join_idem : ∀ a, join a a = a
```

The old hierarchy nested idempotence under commutativity, "for one class fewer," even though neither `foldG_le` nor `foldG_cons_ne_nil` ever cites commutativity. That was a real, silent cost: both theorems ended up requiring commutativity as a hypothesis they never used, exactly what my own rule about taking the weakest hypothesis that proves a theorem says not to do. Splitting them apart fixes that without changing either theorem's name or conclusion. The fourth class, `IsCanonicalPomonoid`, bundles both properties as its own fields, and nothing in the file takes it as a hypothesis - it exists only so I have a name for what a real grade like `Grade Err` actually is, distinct from what any single law needs.


# Back in C++

The honest version of Letter 14's question, once this is done, is: does `error_set` have to be a join-semilattice because `and_then` or `apply` need it, or because of a promise the **type** makes? The classification says the second. Sequencing two graded computations, applying a graded function to a graded argument, and traversing a container never need `error_set<X,Y>` and `error_set<Y,X>` reconciled, or `error_set<X,X>` collapsed to `error_set<X>`, as a computation. Those two facts matter for a different reason: they're what makes `error_set<X,Y>` and `error_set<Y,X>` the **same compiler-visible type**, so two call sites written differently but meaning the same error set get types the compiler agrees are equal. That's a promise about identity, not behavior.

The one place this doesn't fully resolve is `traverse`. Its own signature - "the grade doesn't grow with the container's length" - does seem to need a semilattice's worth of structure somewhere, either handed to it for free (if the grade already is one) or bought separately with an idempotence axiom (if it's merely an ordered monoid). I didn't settle which of those P3200 should require; that's a decision about what a grade is allowed to be, not something the algebra decides on its own. What I can say is that it's the **only** place left where the question still bites - `and_then` and `apply` don't care either way.

&ndash;SMD
