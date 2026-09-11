::: add

::: wording

## Operations [transpose.errset.ops]{- .sref} {-}

```cpp
friend auto operator==(const error_set_of&, const error_set_of&) -> bool = default;
```

[x]{.pnum} *Returns*: `true` if and only if both operands witness the same set of alternatives and the corresponding witnesses compare equal.

[x+1]{.pnum} *Remarks*: Equality is what keeps a graded carrier as usable as an ungraded one: `expected<T, E>` compares equal whenever `E` does, and a graded `expected` would silently lose that were this absent. Defaulted, so it is deleted rather than ill-formed when an alternative is not equality-comparable.

```cpp
constexpr auto combined_with(const error_set_of& other) const -> error_set_of;
```

[x+2]{.pnum} *Returns*: A value at the same grade witnessing every alternative either operand witnesses.

[x+3]{.pnum} *Remarks*: Combination is left-biased per alternative: where both operands witness the same error type, `*this`'s witness is kept. This is the evidence-combining step of accumulating composition.

```cpp
template<>
class error_set_of<> {
public:
  // @[transpose.errset.empty]{- .sref}@, the empty error set
  error_set_of() = delete;

  template<class ERROR> static constexpr auto contains() noexcept -> bool;
};
```

:::

:::
