# Letter 20: The function that existed only to prove a length didn't matter

Steve,


# What I set out to do

Letter 19 closed with one loose thread. Every citation of commutativity or idempotence in the model turned out to be about a grade's spelling, never about a value a computation picks, with one exception left open: `traverse`. Its whole point is that the error set doesn't grow with the list's length, and that length-independence looked like it might actually need a semilattice, not just get to use one for free the way `and_then` and `apply` do.

This letter answers it by building the same cast-free layer Letters 17 and 18 built for `and_then` and `apply`, now for `traverse`, and asking a sharper question than "do the casts go away": does `foldGrade`, the function that folds a grade into itself once per element, have any analogue at all once the caller nominates the target grade instead of asking Lean to compute it? If a caller says up front "land in this grade `k`, which I already know is big enough," nobody ever needs to fold anything, because there's nothing to fold towards.


# What the checker refused

I wrote the three reduction lemmas for the new `traverseK`'s cons case (one per shape: element ok/tail ok, element err, tail err) the way every earlier reduction lemma in this layer had gone, by rewriting through the definition and a hypothesis pinning down the shape:

```lean
theorem traverseK_cons_ok_ok (hg : g ⊆ k) (f) (x) (xs) (b) (l)
    (hfx : f x = Graded.ok b) (hxs : traverseK hg f xs = Graded.ok l) :
    traverseK hg f (x :: xs) = Graded.ok (b :: l) := by
  rw [traverseK_cons, hfx, hxs]
```

Every earlier lemma of this exact shape in the file closes right there, because `rw` tries a plain reflexivity check once it's out of rewrites to do. This one didn't. Lean left an "unsolved goals" error naming the literal `map2K` application as the remaining goal. Nothing was wrong with the fact; `map2K hg (Grade.le_refl' k) (· :: ·) (ok b) (ok l)` really does equal `ok (b :: l)`, definitionally. What `rw`'s trailing check won't do is unfold a `def` like `map2K` to see that. It only inspects the term already in front of it. Adding one more line, a bare `rfl`, which unfolds `map2K` through `apK` through `bindK` all the way down, closed all three lemmas immediately. Small, and easy to fix, but the kind of miss that's honest evidence for the letter's real claim: a layer that turns out to be free doesn't announce that by feeling easy while you write it. It announces it by every single obligation dissolving to `rfl` once you actually check.


# What changed

`traverseK hg f` folds nothing. Every element's image under `f` and the accumulated tail combine at `k` directly, both reusing the same inclusion proof:

```lean
def traverseK (hg : g ⊆ k) (f : α → Graded g β) : List α → Graded k (List β)
  | []      => pureK []
  | x :: xs => map2K hg (Grade.le_refl' k) (· :: ·) (f x) (traverseK hg f xs)
```

`traverseK_map`, the identity law `traverseK_fromEmpty`, and the shape- preservation theorem `traverseK_length` all restate cast-free, each built the same way its union-graded counterpart was, and each cheaper: where `traverse_map=/=traverse_fromEmpty` delegate to `traverse_cons`'s own idempotence cast and rely on it cancelling out, the `traverseK` versions delegate to a `traverseK_cons` that never had a cast to begin with. There is no `foldGradeK` anywhere in the file, and there wasn't a moment where I wanted to write one. Length-independence stopped being a theorem you prove and became a fact about the **signature**: `traverseK hg f : List α → Graded k (List β)` names the same output grade `k` for every list before a single theorem is stated about it.

The one place idempotence still shows up is the bridge, `traverse_eq_ traverseK`, which instantiates `traverseK` at the tightest possible sufficient grade (`g` itself, sufficient for itself) and shows it equals the union-graded `traverse`. That equation still has to go through `traverse_cons`'s own cast, because `traverse`'s intermediate step really does compute `g ⊔ g` and identify it with `g`. The idempotence isn't reconciling `traverse` against `traverseK`; it's `traverse` reconciling two spellings of its own grade, exactly as Letter 19 already found, with `traverseK` sitting outside that reconciliation entirely.


# Back in C++

`foldGrade` and `foldGrade_cons_ne_nil` exist to answer a question a compiler asks itself when it writes `traverse`'s return type by folding: "after joining this error set into itself once per element of a list whose length I don't know yet, is the answer still just the one error set I started with?" That's a real question, and answering it costs idempotence, because folding is genuinely happening. But it's a question only worth asking because the return type is being **computed**. A caller who instead writes something closer to `traverse_as<Es>(f, xs)`, naming the error set up front the way a sufficient grade does here, never asks it. The compiler's job shrinks to checking that each element's error type is a member of `Es`, once per element, and that check doesn't grow or shrink with the list's runtime length either way, because nothing about it was ever a fold. The function evaporates not because someone optimized it away, but because the caller answered its question before it could be asked.

&ndash;SMD
