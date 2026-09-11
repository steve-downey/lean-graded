::: add

::: wording

## Transposing a tuple of arrays [transpose.array.tuple]{- .sref} {-}

```cpp
template<size_t N, class... Ts>
auto transpose_tuple(const tuple<array<Ts, N>...>& soa) -> array<tuple<Ts...>, N>;
```

[x]{.pnum} *Effects*: Transposes a tuple of arrays into an array of tuples: the element at position `i` of the result is the tuple of the elements at position `i` of each operand array.

[x+1]{.pnum} *Returns*: That array of `N` tuples.

[x+2]{.pnum} *Complexity*: Linear in `N`.

[x+3]{.pnum} *Remarks*: This is a heterogeneous traversal. Each operand array may have a different element type, so the homogeneous traversable loop, which requires one element type, does not apply; the composition is over the tuple positions instead, through the array applicative object.

:::

:::
