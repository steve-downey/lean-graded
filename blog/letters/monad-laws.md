# Letter 4: The monad laws are true up to something, and Lean wants to know up to what

Steve,


# What I set out to do

You've chained `and_then` calls before: `parse(s).and_then(check_range)`, and the compiler works out that the result's error set is the union of `parse`'s and `check_range`'s. Nobody writes down what makes that chaining **lawful**: that composing three calls left-to-right gives the same answer as composing them right-to-left, that a call which can't fail is a no-op in the chain. You just trust it, the way you trust that adding zero doesn't change a number.

I wanted to write those trust assumptions down as theorems: the three monad laws. `pure` puts a value in with an empty error set; `bind` sequences two graded computations into one, at the **union** of their two grades. The three laws say `bind (pure a) f` is just `f a`, that binding into `pure` is a no-op, and that re-associating three chained binds doesn't change the answer. In C++ these are true because the compiler's type canonicalization makes the two sides' types **the same type**; you'd never notice there was anything to prove. In Lean, the union of two grades is a genuine `Finset` union, and `∅ ∪ h` is only **equal** to `h`, not the same expression, so each law needs a companion proof of a grade equation, plumbed through with a conversion function called `cast`. This step's real question was whether that plumbing would be bearable, or whether it would swallow every proof in bookkeeping.


# What the checker refused

Every law it refused, it refused for the same reason. My first attempt tried to state the fully-reduced goal directly using a tactic called `show` ("the goal is actually this, trust me") and got the **substituted-in** term wrong in several places, because I'd hand-simplified a nested pattern match faster than I could keep straight in my head. Lean's answer each time was precise: "the argument you gave has this type, but I needed that one," a mismatch between which error set a proof was evidence for.

The fix wasn't a cleverer tactic, it was writing three small reusable lemmas first, each proved the same way:

```lean
theorem cast_ok (e : g = g') (a : α) :
    cast e (Graded.ok a : Graded g α) = Graded.ok a := by
  subst e; rfl
```

`subst e` is the same substitution tactic from Letter 3's `widen_cast`: it uses the equality proof to make both sides talk about the same grade, and `rfl` closes it because a value carries no evidence of which grade it's tagged with. I wrote two more in the same shape, one for the failure case and one for the "widen, then convert" case, and every law after that became: split on whether the input succeeded or failed, restate the fully reduced goal with Lean's `change` tactic (its whole job is "the goal is this, and I can prove it's the same goal." Unlike `show`, it insists on checking that, which is what caught my mistakes), and close with one of the three small lemmas.

The other decision the step asked me to make myself was which way a `cast` should point in each law's statement: toward the plain form or its mirror image, using a proof or its reverse. I picked whichever direction meant the **messier** expression (the one with the visible `join`) collapsed down to the tidy one, using each grade equation exactly as it's already written. That turned out to always be possible, so no law needed a reversed proof anywhere, including in the tests that use them.


# What changed

`Graded/Monad.lean` now has `pure`, `bind`, and five theorems: the two unit laws, associativity, one saying that mapping a function over a graded value is the same as binding into a `pure` wrapping it, and one saying that widening a value before binding it agrees with widening after. That last one needed no `cast` at all: widening produces a proof of **inclusion**, not equality, so both sides land at literally the same grade.

I also went back to the two-stage validation from an earlier letter and replaced the by-hand composition (the `match` that manually assembled the union error set) with a single call to `bind`. The three example outputs ("ok 42", "err parse", "err range") came out identical, which is exactly the point: the hand-written version and the `bind`-based version were always supposed to be the same function, and now that's not just asserted, it's the same three-line definition doing the work every other `and_then` chain will use.


# Back in C++

What stuck with me: the C++ `and_then` for this instance never once mentions that `∅ ∪ Es` is `Es`. It doesn't have to, because `error_set<>` and `error_set<Es...>` canonicalize down to literally the same alias, and the compiler's type checker treats "same type" as free. What I did this step was take that free fact and pay for it explicitly: name it (`bot_join`), state where each law needs it, and write the three-line proof that pushes it through. It's the same fact, expressed as a runtime-free type identity on one side and a checked theorem on the other.

Given the choice, I'd rather debug the Lean version. A type identity that "just works" fails silently the day someone's refactor breaks the canonicalization: the union no longer collapses to the alias you expected, and you find out from a wall of template errors three call sites away. A named theorem fails right where the assumption stops holding, with a statement you can read. The C++ approach costs nothing until it costs everything at once; the Lean approach costs a little every time, and never surprises you.

&ndash;SMD
