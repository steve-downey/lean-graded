# Letter 22: Flatten still computes a grade, and commutativity finally ran out of places to hide

Steve,


# What I set out to do

This is the last leg of the sufficient-grade run, and it is the one I was least sure would go the same way as the others. Every operation so far got cheaper by letting the caller name the result grade instead of computing it: `and_then` stopped computing a union, `apply` stopped computing a union, `traverse` stopped folding one. `flatten` is different. Its entire job is to take a value nested two grades deep and collapse it to one grade, so a caller-nominated version does not remove the grade arithmetic, it only removes the requirement to name the union specifically. I did not know ahead of time whether there would be anything left to say about swapping the two layers once both of them already land at the same caller-chosen grade, or whether the law that says so would just disappear.

The second thing I was watching for was smaller to state and bigger if it turned out to be true: one grade equation in this whole model, `Comp.grade_reassoc`, was the last place a commutativity fact still sat inside an operation about actual values rather than a pure claim about two spellings of a grade. If its sufficient-grade version turned out to be unnecessary, the model would contain no operational use of commutativity anywhere. That is the sentence I wanted to be able to write honestly, not assume.


# What the checker refused

The proof that gave me the most trouble was the sufficient-grade version of "is flatten an applicative morphism," which combines two nested values and then either flattens the combined result or flattens each piece first. I wrote out all the cases by hand before touching Lean, and still got one branch wrong on the first try:

```lean
| ok f' =>
    simp only [Comp.apK_ok_err, flattenK_ok, flattenK_err, widen_err, apK_ok_err]
```

Lean left a goal with `widen (proof) (Graded.ok f')` sitting in it, unreduced, on the left of the equation I was trying to prove. I had told the simplifier how to finish widening an **error**, because that is what the right-hand side needed, and forgot the left-hand side needed the **success** case of the same function. Once I added that back in, both sides collapsed the same way. It was a reminder that "the same tactic worked in the last three branches" is not evidence it will work in this one; each branch touches the success and failure case of two different values, and forgetting one of the four combinations shows up as a leftover unreduced term rather than a clean error message.


# What changed

`flattenK` is built the same way `flatten` itself is described, just one level more literally: instead of proving `flatten` equals `bind` applied to the identity function, I defined `flattenK` to **be** `bindK` applied to the identity function. Every law that carried a cast before (collapsing an empty outer layer, collapsing an empty inner layer, reassociating three nested layers) now states with none, for the same reason every earlier leg found: there is only one grade in the statement, not two spellings of the same one to reconcile.

The swap law was the surprise. At a computed grade, "flatten agrees with flatten after swapping the layers" needs a cast, because swapping changes which grade comes first. At a caller-chosen grade, both sides already land in the same type before you even look at the proof, and the equation turns out to be true by direct computation in every case, no side condition at all. That is a stronger result than merely losing a cast: there was no property left to state.

`Comp.grade_reassoc` confirmed the bigger claim. That theorem exists for exactly one reason: to make a cast typecheck in the applicative- morphism law above, reassociating two grades that get computed in a different order on each side. The sufficient-grade version of that law never produces a cast in the first place, so there is nothing for a reassociation fact to serve, and none is missing. With that gone, and the swap law needing nothing either, the sufficient-grade layer now has zero operational uses of commutativity anywhere in it.

One thing did not simplify, and it should not have. The applicative- morphism law still needs the same three-way condition on which value actually failed, spelled out exactly as before. I built a concrete counterexample where that condition fails, on purpose, to check the two sides genuinely disagree rather than the law becoming true for free. They do disagree, rendering two different error kinds from the same inputs. That was worth checking directly rather than trusting that a shorter statement is automatically a correct one.


# Back in C++

The practical claim this leaves for `error_set` is a narrow, checkable one: nothing in `and_then`, `apply`, `transpose`, or a nested `expected`'s collapse ever needs `error_set<A, B>` and `error_set<B, A>` to be recognized as the same type in order to compute the right answer. Every place that recognition mattered turned out to be paperwork created by computing the exact union and then discovering you'd written it two different ways, never a decision about which error a caller actually sees. A design that tracks "a set big enough to hold everything" instead of "the exact union, canonically spelled" never generates that paperwork in the first place. What does not go away, and should not, is the question of which error wins when two things can independently fail. That is not grade bookkeeping. It is the actual behavior of the program, and no amount of nominating a bigger error set changes it.

&ndash;SMD
