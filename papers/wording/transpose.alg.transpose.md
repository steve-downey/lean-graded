::: add

::: wording

## transpose [transpose.alg.transpose]{- .sref} {-}

```cpp
template<class T> auto transpose(T&& value);
```

[x]{.pnum} *Constraints*: `traversable_typeclass` names a traversable object for `value`'s type, and `applicative_typeclass` names an applicative object for that structure's element type.

[x+1]{.pnum} *Effects*: Equivalent to traversing `value` with the identity function: a structure of contextual values, `structure<context<T>>`, becomes a single contextual value of the structure, `context<structure<T>>`, preserving shape. The applicative object is inferred from the structure's element type.

[x+2]{.pnum} *Returns*: That single contextual value.

[x+3]{.pnum} *Complexity*: Linear in the number of elements of `value`.

[x+4]{.pnum} *Remarks*: Elements are visited in the structure's iteration order, and their contexts are composed in that same order.

:::

:::
