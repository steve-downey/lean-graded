# Letter 6: Same grade, twice as many errors

Steve,


# What I set out to do

Last letter ended on a promise: if you want to **collect** every failure instead of stopping at the first, that has to be a different applicative, built on purpose, not inherited for free from the monad. This is that applicative (the one most people mean when they say "Validation"): run two independent checks, and if both fail, report both.

The question I actually had to answer first wasn't "does this work," it was "can it live in the same box." Our `expected`-like type, `Graded g α`, holds **one** value or **one** error. That's not an implementation detail I could work around: it's the whole point of the type, the thing that lets a single error carry a single proof that its kind belongs to the grade `g`. An accumulating `ap` that fails on both sides has two errors to report and one slot to put them in. Something has to give, and I went in expecting the answer to be "a second type," not "a cleverer way to pack two errors into one."


# What the checker refused

The prediction held: I built a second carrier, `Accum g α`, holding either a value or a **non-empty list** of errors, each one still a member of the grade `g`. Concatenating two such lists when both sides fail was the easy part. What the checker refused was my first attempt at proving the "three things compose the same way regardless of how you parenthesize them" law, once I got to the one case where **all three** of the things being composed have failed.

Every other applicative law here needed exactly what the plain `Graded` version needed: unit and associativity facts about the grade, nothing about commutativity. This one case needed something new: the two sides of the law build the **same** list of accumulated errors, but one builds it as `(a ++ b) ++ c` and the other as `a ++ (b ++ c)`. Lean does not consider those the same term just because list append happens to be associative: that's a fact you have to invoke, `List.append_assoc`, not something the definition of append gives you for free. I'd written the proof assuming the two sides would just match once I'd unfolded enough definitions; they didn't, until I added that one lemma.

The bigger surprise came from a theorem I expected to **need** a restriction and it turned out not to. I define a way to collapse an `Accum` back down to a `Graded` (take the first error, if there is one), and I expected that collapsing **after** accumulating would disagree with collapsing **before** and then combining, exactly the same way last letter's `ap` and `apFlipped` disagreed once both sides could fail. I wrote the restricted version first, matching that earlier condition ("at most one side failed"). Then I tried the unconditional version, out of curiosity about how badly it would fail on the both-failed case. It didn't fail at all.


# What changed

The reason is almost embarrassingly simple once you see it. My accumulating `ap` concatenates the function's errors **before** the argument's errors, because that matches the order you already apply things in: function, then argument. And the plain `Graded` applicative, built from sequencing, **always** keeps the function's error when the function has failed, no matter what the argument does. Put those two facts side by side: "the first error in the accumulated list" and "the error the collapse-then-combine path reports" are, by construction, the exact same error.

```lean
theorem toGraded_grade' (f : Accum g (α → β)) (x : Accum h α) :
    toGraded (ap f x) = Graded.ap (toGraded f) (toGraded x) := by
  ...
```

No hypothesis needed at all: I kept both theorems, the restricted one and this one, because the restricted one is still the honest answer to "does this match the condition from last letter's finding" (it does, word for word), even though it turned out not to be load-bearing here. Had I concatenated the other way round (argument's errors first), the two would have disagreed on the both-failed case, and I'd have needed the restriction after all. The condition is real; whether a given pair of definitions actually needs it is a separate question, and I got the answer to that one wrong going in.

The other piece worth a letter of its own: proving `Accum` genuinely **isn't** a monad. It's not merely that I didn't happen to build a `bind` for it; no `bind` can exist. The honest argument doesn't need anything exotic; it needs one failing input whose payload type happens to be a function into an uninhabited type. Any candidate `bind` handed that input has, as its continuation, a function with no possible argument to apply it to; and any two functions with no possible argument are the same function, whatever they're supposedly "about." So a candidate `bind` genuinely cannot tell an argument that succeeded from one that failed with a second error, except that my accumulating `ap` **does** tell them apart, on purpose. No `bind` can match it.


# Back in C++

`expected` cannot accumulate, for the same reason `Graded` couldn't: one error slot. If the committee ever wants a Validation-style `traverse` (collect every field's error instead of stopping at the first), the right answer is not a cleverer `expected` but a genuinely different type, built to hold more than one error, connected back to `expected` by an explicit "take the first" conversion rather than an implicit one. And now there's a precise answer to "when does it matter which type you used": exactly when more than one thing you combined could actually have failed. One failure, and the two views agree on what happened; more than one, and only the accumulating type tells you the whole story.

&ndash;SMD
