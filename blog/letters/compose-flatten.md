# Letter 9: Nested expecteds and the distributive law nobody wrote down

Steve,


# What I set out to do

You've written this before without thinking twice about it: `expected<expected<T, error_set<Parse>>, error_set<Io>>` collapsing to `expected<T, error_set<Io, Parse>>`. An I/O stage that can fail wraps a parse stage that can fail, and you flatten the two down to one, with one combined error set. It looks obviously safe. I wanted to know what "safe" actually costs: does the flattening play nicely with mapping a function over the payload, with combining it with `and_then`, with widening either layer to a bigger error set before or after you flatten it? And the more interesting question: if you flatten **inside** a loop (traverse a whole container of these fetch-then-parse results), does flattening each one first and then combining across the container give you the same answer as combining across the container first and flattening once at the end?


# What the checker refused

The first refusal was small and mechanical. I wanted to state that flattening a nested value is exactly the same operation as `and_then` with the identity function: the "it's just the monad's own multiplication" fact. Lean rejected the statement outright, before it even got to checking a proof, over the same kind of universe accounting from Letter 8's `GList`: a `Graded h α` value (the inner, still-nested carrier) is **strictly bigger**, in that sense, than the plain payload `α` it will eventually flatten down to. The existing `and_then` was written expecting its "before" and "after" payload types to be the same **size** of type, which is true every time you call it directly, and stopped being true the moment I asked it to accept another `Graded` as the payload. It's the C++ equivalent of a function templated to take a small integer type on both sides of an operation, and you handing it a type built out of two of them stacked together.

The second refusal was bigger, and it was actually right to refuse. My best guess at "the composition law" read: flatten each nested result after combining the whole container with the inner function, and that should equal combining the container with a function that flattens as it goes, one element at a time. I tried to prove it by cases and found a genuine counterexample instead:

```lean
def f : Bool → Graded g Nat        -- succeeds on `true`, fails on `false`
def k : Nat → Graded h Nat         -- always fails

#eval renderLookup (flatten (map (traverse k) (traverse f [true, false])))  -- err (f's failure)
#eval renderLookup (traverse (fun a => flatten (map k (f a))) [true, false]) -- err (k's failure)
```

Two elements: the first succeeds at the outer stage and then fails at the inner one; the second fails at the outer stage outright. Combine everything at the outer stage first, then the inner stage second, and you report the **second element's** outer failure: you never even reach the inner stage, because the outer combination already gave up. Flatten each element as you go, and you report the **first element's** inner failure, because now every element looks like one flat "did something go wrong" value, and the container just reports whichever one failed first, regardless of which stage it was.


# What changed

The universe refusal I could fix locally: this one file's payload types now live at the same size as the error-kind universe itself, which happens to make the troublesome equation true by definition rather than by proof, and nothing outside this file noticed the change.

The composition law I couldn't fix, because it isn't true, so I didn't try to weaken it into something provable. What I did keep, and what surprised me, was a related question about reordering the two layers instead of composing them across a container. I expected flattening to commute with swapping inner and outer only when at most one layer actually held an error, the same hedge I'd already needed twice before, once for combining two independent function-and-argument results and once for combining a tuple of independent results. It turned out that hedge was never needed here at all: a nested value only ever holds **one** live error to begin with: there's no way to construct one with both layers failing at once, unlike two genuinely separate results that can each fail independently, so the swap is safe unconditionally.


# Back in C++

The safe part of this letter is safe: flattening a nested `expected` really does commute with mapping, with wrapping either layer in a trivial success, with re-flattening a triple-nested one from either end, and with widening either layer's error set first. All of that you can rely on the way you already do, without having to check which layer might have failed.

The part worth slowing down for is the loop. If you write a function that fetches then parses, returning one flattened `expected` per element, and you run it across a `std::vector` with a short-circuiting `transpose`, you'll get "the first element whose fetch-or-parse failed, whichever came first, no matter which stage." That's very likely what you want. But if your code is instead structured as two separate passes (gather all the fetches into a vector of raw results, check that whole vector for any failure, and only then parse the ones that came back), you are running a **different** algorithm, one that always prefers a fetch failure over a parse failure, anywhere in the container, even one that occurs after a fetch failure earlier in the list would have short- circuited the single-pass version first. Both are reasonable designs. They are not the same design, and nothing about `expected<expected<T, E1>, E2>` being "obviously" flattenable to `expected<T, E1 ∪ E2>` tells you which one you've written.

&ndash;SMD
