::: add

::: wording

## Traversal operations [transpose.traversable.ops]{- .sref} {-}

```cpp
template<class T, class F> auto for_each(this auto&& self, T&& value, F&& function);
```

[x]{.pnum} *Effects*: Applies `function` to each element of `value` and transposes the resulting contextual values, preserving the shape of `value`. The applicative object is the one `applicative_typeclass` names for the context `function` returns.

[x+1]{.pnum} *Returns*: The shape of `value` held in that single context.

[x+2]{.pnum} *Complexity*: Exactly one application of `function` per element of `value`.

[x+3]{.pnum} *Remarks*: Elements are visited in the structure's iteration order.

```cpp
template<class T> auto transpose(this auto&& self, T&& value);
```

[x+4]{.pnum} *Constraints*: `element_type` is a context for which `applicative_typeclass` names an applicative object.

[x+5]{.pnum} *Effects*: Equivalent to traversing `value` with the identity function: a structure of contextual values becomes a single contextual value of the structure, preserving shape.

[x+6]{.pnum} *Returns*: That single contextual value.

[x+7]{.pnum} *Remarks*: Elements are visited in the structure's iteration order.

:::

:::
