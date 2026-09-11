::: add

::: wording

## Traversable instance for vector [transpose.range.traverse]{- .sref} {-}

```cpp
template<class APPLICATIVE, class FUNCTION>
auto traverse(this auto&&, const APPLICATIVE& applicative, FUNCTION&& function,
              const vector<VALUE_TYPE>& values);
```

[x]{.pnum} *Effects*: Applies `function` to each element of `values` in order and composes the resulting contextual values with `applicative`, collecting the element results into a `vector`.

[x+1]{.pnum} *Returns*: A `vector` of the element results, of the same size as `values` and in the same order, held in the single context `applicative` composes into.

[x+2]{.pnum} *Complexity*: Exactly `values.size()` applications of `function`.

[x+3]{.pnum} *Remarks*: Traversal preserves shape: the result holds one element per element of `values`, in the same order. Elements are visited in the vector's iteration order, and their contexts are composed in that same order.

:::

:::
