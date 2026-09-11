::: add

::: wording

## Observers [transpose.errset.obs]{- .sref} {-}

```cpp
template<class ERROR> static constexpr auto contains() noexcept -> bool;
```

[x]{.pnum} *Returns*: `true` if and only if `ERROR` is one of the alternatives.

[x+1]{.pnum} *Remarks*: This is a type-level question -- what the computation *may* raise -- not a question about the value.

```cpp
template<class ERROR>
  requires($error-set-has-v$<ERROR, ERRORS...>)
constexpr auto holds() const noexcept -> bool;
```

[x+2]{.pnum} *Constraints*: `ERROR` is one of the alternatives.

[x+3]{.pnum} *Returns*: `true` if and only if this value witnesses `ERROR`.

[x+4]{.pnum} *Remarks*: This is a value-level question -- what was actually raised.

```cpp
template<class ERROR>
  requires($error-set-has-v$<ERROR, ERRORS...>)
constexpr auto witness() const -> const optional<ERROR>&;
```

[x+5]{.pnum} *Constraints*: `ERROR` is one of the alternatives.

[x+6]{.pnum} *Returns*: The witness for `ERROR` if this value raised it, and a disengaged `optional` otherwise.

```cpp
constexpr auto witness_count() const noexcept -> size_t;
```

[x+7]{.pnum} *Returns*: The number of alternatives this value witnesses.

[x+8]{.pnum} *Remarks*: Always at least one, by the class invariant. Short-circuiting composition produces exactly one; accumulating composition may produce more. It is an observer rather than an implementation detail so that a caller can check `visit`'s precondition instead of tripping it.

```cpp
template<class HANDLER> constexpr auto visit;
```

[x+9]{.pnum} *Preconditions*: `witness_count()` is 1.

[x+10]{.pnum} *Effects*: Invokes `handler` with the single witnessed value.

[x+11]{.pnum} *Returns*: The result of that invocation.

[x+12]{.pnum} *Remarks*: The precondition is checked rather than assumed. Every value produced by short-circuiting composition satisfies it; a subset with more than one witness, which only accumulating composition produces, has no single value to hand back, and answering with the leftmost would turn a dropped error into a quiet wrong answer. For such a value, use `witness` per alternative, guarded by `holds` or `witness_count`.

:::

:::
