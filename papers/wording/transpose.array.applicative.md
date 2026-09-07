::: add

::: wording

## Applicative instance for array [transpose.array.applicative]{- .sref} {-}

```cpp
template<class VALUE> auto pure(this auto&&, VALUE&& value);
```

[x]{.pnum} *Returns*: An `array<remove_cvref_t<VALUE>, N>` each of whose `N` elements is a copy of `value`.

```cpp
template<class FUNCTION, class FIRST, class... REST>
auto invoke(this auto&&, FUNCTION&& function, const FIRST& first, const REST&... rest);
```

[x+1]{.pnum} *Returns*: An `array` of `N` elements whose element at position `i` is the result of invoking `function` with the element at position `i` of each operand.

[x+2]{.pnum} *Complexity*: Exactly `N` applications of `function`.

[x+3]{.pnum} *Remarks*: Application is positional: operands are combined lane by lane, and every operand has the same fixed extent `N`.

:::

:::
