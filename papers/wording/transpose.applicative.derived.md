::: add

::: wording

## Derived operations [transpose.applicative.derived]{- .sref} {-}

```cpp
template<class FUNCTION, class ARGUMENT>
auto map(this auto&& self, FUNCTION&& function, ARGUMENT&& argument);
```

[x]{.pnum} *Constraints*: `Impl` provides either a `map` accepting `function` and `argument`, or an `invoke` accepting `function` and `argument`.

[x+1]{.pnum} *Effects*: If `Impl` provides `map`, the effect is that of `Impl`'s own `map`; otherwise the application is expressed through `Impl`'s `invoke`.

[x+2]{.pnum} *Returns*: The single value in context holding the result of applying `function` to the value held by `argument`.

```cpp
template<class VALUE> auto lift(this auto&& self, VALUE&& value);
```

[x+3]{.pnum} *Constraints*: `Impl` provides either a `lift` accepting `value`, or a `pure` accepting `value`.

[x+4]{.pnum} *Effects*: If `Impl` provides `lift`, the effect is that of `Impl`'s own `lift`; otherwise `value` is lifted into the context using `Impl`'s `pure`.

[x+5]{.pnum} *Returns*: The single value in context holding `value`.

```cpp
template<class FUNCTION, class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto zip_with(this auto&& self, FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
              SECOND_ARGUMENT&& second_argument);
```

[x+6]{.pnum} *Constraints*: `Impl` provides either a `zip_with` accepting `function` and the two arguments, or an `invoke` accepting `function` and the two arguments.

[x+7]{.pnum} *Effects*: If `Impl` provides `zip_with`, the effect is that of `Impl`'s own `zip_with`; otherwise the application is expressed through `Impl`'s `invoke`.

[x+8]{.pnum} *Returns*: The single value in context holding the result of applying `function` to the values held by `first_argument` and `second_argument`.

```cpp
template<class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto discard_first(this auto&& self, FIRST_ARGUMENT&& first_argument,
                   SECOND_ARGUMENT&& second_argument);
```

[x+9]{.pnum} *Constraints*: `Impl` provides either a `discard_first` accepting `first_argument` and `second_argument`, or an `invoke` accepting a callable that ignores its first parameter and returns its second, together with `first_argument` and `second_argument`.

[x+10]{.pnum} *Effects*: If `Impl` provides `discard_first`, the effect is that of `Impl`'s own `discard_first`; otherwise the application is expressed through `Impl`'s `invoke`, applying a callable that discards the value held by `first_argument` and returns the value held by `second_argument`.

[x+11]{.pnum} *Returns*: The single value in context holding the value that `second_argument` holds.

```cpp
template<class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto discard_second(this auto&& self, FIRST_ARGUMENT&& first_argument,
                    SECOND_ARGUMENT&& second_argument);
```

[x+12]{.pnum} *Constraints*: `Impl` provides either a `discard_second` accepting `first_argument` and `second_argument`, or an `invoke` accepting a callable that returns its first parameter and ignores its second, together with `first_argument` and `second_argument`.

[x+13]{.pnum} *Effects*: If `Impl` provides `discard_second`, the effect is that of `Impl`'s own `discard_second`; otherwise the application is expressed through `Impl`'s `invoke`, applying a callable that returns the value held by `first_argument` and discards the value held by `second_argument`.

[x+14]{.pnum} *Returns*: The single value in context holding the value that `first_argument` holds.

:::

:::
