# Letter 17: The casts were telling me something, and it wasn't 'clean me up'

Steve,


# What I set out to do

I said Letter 16 was the last one. It wasn't: a review of all sixteen together found something the letter-by-letter view had missed. Letter 4 measured the cast burden in `bind`'s three laws and called it "tolerable, not dominating." Right for `bind` alone, wrong as a claim about the whole model: count the layers built on top of it and 39 of 146 theorems (26%) carry a `cast`, one statement carries six at once, and one record type has `cast`-quantified fields. So this letter asks the question Letter 4 answered too early: is there a way to state these laws with no `cast` at all, and if so, why didn't I do that the first time?


# What the checker refused

Nothing new this time. What "the checker refused" is the same thing it refused in Letter 4; I want to show its actual shape rather than wave a hand at "the union grades don't line up." Here is `bind`'s associativity law, twice: first as I wrote it in Letter 4, then the shape it would have if C++'s type canonicalization simply didn't exist.

```lean
-- as stated (with cast):
cast (Grade.join_assoc g h j) (bind (bind x f) k) =
  bind x (fun a => bind (f a) k)

-- what it would say if (g ∪ h) ∪ j and g ∪ (h ∪ j) were the same
-- expression, not just equal sets:
bind (bind x f) k = bind x (fun a => bind (f a) k)
```

Both sides of that second version typecheck against different grades. The left side's result lives at `(g ∪ h) ∪ j`; the right side's at `g ∪ (h ∪ j)`. Those two sets have the same elements, and `Finset.union_assoc` proves it, but they are not the same expression, and Lean will not let a value of one type stand where the other is expected without saying why. C++ never makes you say why: whichever way `error_set<parse, range, io>` happened to nest, it canonicalizes to the identical type alias, and the compiler treats "same type" as free. Lean charges for it honestly, every time, with a `cast` and a proof.


# What changed

The obvious fix, once you have stared at that cast long enough, is to stop computing the grade: let the caller say "I know both sides fit in `k`," supply two proofs of that, and skip the union arithmetic. I want to name why that is a trap, because it is the most useful thing in this letter and the reason the casts survived twelve steps before anyone seriously proposed removing them. Letting the caller nominate the result grade instead of computing it quietly builds a different `and_then` than the one P3200 specifies, whose real one always computes the union; that's why the type gets wider as you chain more calls. A version that lets the caller ask for any grade "big enough" is not a cleaned-up version of that operation. It is a different operation that happens to agree with it sometimes. Removing every cast by switching to it would make the model prettier and less true.

So instead I built both, side by side. `bind` stays exactly as it was, computing `Grade.join g h`, casts and all; nobody's proof about it changed. Beside it, `bindK` takes two proofs, `g ⊆ k` and `h ⊆ k`, and lands directly in `Graded k β`:

```lean
def bindK (hg : g ⊆ k) (hh : h ⊆ k)
    (x : Graded g α) (f : α → Graded h β) : Graded k β :=
  match x with
  | .ok a     => widen hh (f a)
  | .err e he => .err e (hg he)
```

`widen` carries an error's admissibility proof along a wider inclusion; here it moves `f a`'s result up from `h` to `k`. Because `k` is never equal to a computed expression, only at least as big, there is no equation left to transport, and all three monad laws for `bindK` come out with zero casts: the associativity law above is thirteen proof lines instead of twenty-one, and the other two drop to one line and three. One theorem, `bind_eq_bindK`, ties the two together: instantiate `bindK`'s `k` at the exact union, using the same two inclusions `bind` already carries internally, and you get `bind` back, by `rfl`. Same operation, two views.

The best result was not the missing casts. It was a second theorem, `bindK_irrel`: which proof of `g ⊆ k` you hand in does not matter, also by `rfl`. That is what makes the two threaded proofs a call site pays actually free: nothing downstream has to remember which witness was used, the way nothing has ever had to remember which implicit conversion sequence C++ picked. Had that lemma not gone through by `rfl`, this whole design would trade one bookkeeping cost for another, worse one, and I would be writing you a different letter.


# Back in C++

The honest accounting: for `bind` specifically, the two-layer approach won outright. No casts, shorter proofs, the threaded obligations free. I am recommending it get tried on the applicative layer next, where the cast counts are worse than `bind`'s ever were. But I am not declaring victory for the whole model from one operation. There is a specific thing `bind` never had to face: one applicative law, `ap_flip`, needs the grades to commute, comparing `g ∪ h` against `h ∪ g`, because it compares two orders of the same combination. `bindK` never compares two joins; it never computes a join at all. Whether that commutativity requirement survives the move to a common `k`, or dissolves along with the cast the way associativity did here, is a question this letter's evidence cannot answer. I would rather say that plainly and let the next round of proofs decide it than round a win on one operation off into a verdict on four.

&ndash;SMD


# Correction

[Later: the "39 of 146" figure here is one too many. The right number is 38. It came from a script that found a theorem's statement by cutting at :=, which swallows the whole proof for theorems written with pattern-matching arms and no := at all. One such theorem in the traversal module mentions a cast in its proof and was counted as carrying one in its statement. The percentage is unchanged at 26%.]
