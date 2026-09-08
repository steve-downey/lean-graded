// include/beman/transpose/fold.hpp                                   -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_FOLD_HPP
#define BEMAN_TRANSPOSE_FOLD_HPP

#include <beman/transpose/detail/typeclass_base.hpp>
#include <beman/transpose/monoid.hpp>

#include <cstddef>
#include <functional>
#include <optional>
#include <type_traits>
#include <utility>
#include <vector>

// EVIDENCE, NOT PROPOSED WORDING. D3200R0 proposes Applicative and
// Traversable; it does not propose Foldable. The fold family (fold_map and
// its derived operations, over structures that are not ranges) is proposed
// by the recursive-tree-algorithms companion paper (Paper D), whose
// motivation it belongs to -- std::ranges::fold_left already covers flat
// sequences. This header ships as proof that the typeclass-object mechanism
// scales to the fold family; treat its surface as implementation evidence.

namespace beman::transpose::detail {

// Identity function for fold composition - no type erasure needed
template <class STATE>
struct IdentityFoldFunc {
    constexpr auto operator()(STATE s) const -> STATE { return s; }
};

// Compose two fold functions without type erasure
template <class F1, class F2>
struct ComposedFoldFunc {
    F1 d_f1;
    F2 d_f2;

    template <class STATE>
    auto operator()(STATE s) const -> STATE {
        return d_f2(d_f1(std::move(s)));
    }
};

// Left fold composition (same order as f1 then f2)
template <class STATE>
struct LeftFoldProgram {
    std::function<STATE(STATE)> d_run;

    auto operator()(STATE state) const -> STATE {
        return d_run(std::move(state));
    }
};

// Template-based version that avoids type erasure - used internally
template <class F>
struct LeftFoldProgramT {
    F d_run;

    template <class STATE>
    auto operator()(STATE state) const -> STATE {
        return d_run(std::move(state));
    }
};

template <class STATE>
struct RightFoldProgram {
    std::function<STATE(STATE)> d_run;

    auto operator()(STATE state) const -> STATE {
        return d_run(std::move(state));
    }
};

// Template-based version that avoids type erasure - used internally
template <class F>
struct RightFoldProgramT {
    F d_run;

    template <class STATE>
    auto operator()(STATE state) const -> STATE {
        return d_run(std::move(state));
    }
};

template <class VALUE_TYPE>
struct First {
    std::optional<VALUE_TYPE> d_value;
};

} // namespace beman::transpose::detail

namespace beman::transpose {

template <class STATE>
struct Monoid<detail::LeftFoldProgram<STATE>> {
    auto identity() const -> detail::LeftFoldProgram<STATE> {
        return detail::LeftFoldProgram<STATE>{[](STATE s) { return s; }};
    }

    auto combine(const detail::LeftFoldProgram<STATE> &lhs,
                 const detail::LeftFoldProgram<STATE> &rhs) const
        -> detail::LeftFoldProgram<STATE> {
        return detail::LeftFoldProgram<STATE>{
            [lhs, rhs](STATE s) { return rhs(lhs(std::move(s))); }};
    }
};

// Template specialization for LeftFoldProgramT - avoids type erasure
template <class F>
struct Monoid<detail::LeftFoldProgramT<F>> {
    auto identity() const
        -> detail::LeftFoldProgramT<detail::IdentityFoldFunc<int>> {
        return detail::LeftFoldProgramT<detail::IdentityFoldFunc<int>>{
            detail::IdentityFoldFunc<int>{}};
    }

    template <class G>
    auto combine(const detail::LeftFoldProgramT<F> &lhs,
                 const detail::LeftFoldProgramT<G> &rhs) const
        -> detail::LeftFoldProgramT<detail::ComposedFoldFunc<F, G>> {
        return detail::LeftFoldProgramT<detail::ComposedFoldFunc<F, G>>{
            detail::ComposedFoldFunc<F, G>{lhs.d_run, rhs.d_run}};
    }
};

template <class STATE>
struct Monoid<detail::RightFoldProgram<STATE>> {
    auto identity() const -> detail::RightFoldProgram<STATE> {
        return detail::RightFoldProgram<STATE>{[](STATE s) { return s; }};
    }

    auto combine(const detail::RightFoldProgram<STATE> &lhs,
                 const detail::RightFoldProgram<STATE> &rhs) const
        -> detail::RightFoldProgram<STATE> {
        return detail::RightFoldProgram<STATE>{
            [lhs, rhs](STATE s) { return lhs(rhs(std::move(s))); }};
    }
};

// Template specialization for RightFoldProgramT - avoids type erasure
template <class F>
struct Monoid<detail::RightFoldProgramT<F>> {
    auto identity() const
        -> detail::RightFoldProgramT<detail::IdentityFoldFunc<int>> {
        return detail::RightFoldProgramT<detail::IdentityFoldFunc<int>>{
            detail::IdentityFoldFunc<int>{}};
    }

    template <class G>
    auto combine(const detail::RightFoldProgramT<F> &lhs,
                 const detail::RightFoldProgramT<G> &rhs) const
        -> detail::RightFoldProgramT<detail::ComposedFoldFunc<F, G>> {
        return detail::RightFoldProgramT<detail::ComposedFoldFunc<F, G>>{
            detail::ComposedFoldFunc<F, G>{lhs.d_run, rhs.d_run}};
    }
};

template <class VALUE_TYPE>
struct Monoid<detail::First<VALUE_TYPE>> {
    auto identity() const -> detail::First<VALUE_TYPE> { return {{}}; }

    auto combine(const detail::First<VALUE_TYPE> &lhs,
                 const detail::First<VALUE_TYPE> &rhs) const
        -> detail::First<VALUE_TYPE> {
        if (lhs.d_value) {
            return lhs;
        }
        return rhs;
    }
};

// Foldable pattern invariants:
// - Generic entry point is fold_map(F, T) via foldable_typeclass<T>.
// - Instances provide an object with fold_map(F, T) and specialize
//   foldable_typeclass<Concrete>.
// - Derived APIs (length, fold_left, fold_right, combine_all, any_of, all_of,
//   empty, to_vector, find_first) live on the same looked-up object.
// - Traversal order is instance-defined but must be coherent per instance.

/** CRTP base for Foldable instances.
 * `Impl` must provide either `fold_map(f, container)` or `fold_right` +
 * `element_type`; all other operations are derived from whichever is the
 * primitive.
 */
template <class Impl>
struct Foldable : protected Impl {
    static_assert(
        !std::is_same_v<Impl, std::false_type>,
        "No foldable_typeclass<T> specialization found. "
        "Specialize beman::transpose::foldable_typeclass<T> for your "
        "type T and provide fold_map(F, T) or fold_right(T, STATE, F) "
        "+ element_type.");
    // Alternate-core: Impl provides either fold_map or fold_right as
    // primitive. Haskell equivalent: {-# MINIMAL foldMap | foldr #-}
    //
    // fold_map and fold_right are a mutually-derivable pair, done the
    // apply.hpp way: each probes Impl for its own native version first, and
    // each derivation addresses Impl directly (impl_of(self), never self)
    // for the other operation. Before this conversion, both derivations were
    // self-routed, and the only thing standing between that and unbounded
    // mutual template recursion -- fold_map deriving from fold_right
    // deriving from fold_map, each round nesting another RightFoldProgram --
    // was a Map's using-declaration happening to shadow one side. A Map that
    // omitted it fell into the cycle. Addressing Impl directly closes that
    // structurally: neither derivation can re-enter the other through self,
    // because self is never named. The Maps' using-declarations are no
    // longer what selects the primitive; the base decides, per
    // instantiation, from whichever basis Impl actually provides.

    // Derived fold_map from fold_right. Requires element_type to deduce the
    // monoid result type. foldMap f = foldr (\x acc -> f x <> acc) mempty
    template <class F, class T>
    auto fold_map(this auto &&self, F &&function, T &&value)
        requires requires(const Impl &impl) {
            impl.fold_map(std::forward<F>(function), std::forward<T>(value));
        } || requires(const Impl &impl) {
            typename Impl::element_type;
            impl.fold_right(std::forward<T>(value),
                            monoid_identity<remove_cvref_t<std::invoke_result_t<
                                F, const typename Impl::element_type &>>>(),
                            [](const auto &,
                               remove_cvref_t<std::invoke_result_t<
                                   F, const typename Impl::element_type &>>
                                   acc) { return acc; });
        }
    {
        if constexpr (requires {
                          impl_of(self).fold_map(std::forward<F>(function),
                                                 std::forward<T>(value));
                      }) {
            return impl_of(self).fold_map(std::forward<F>(function),
                                          std::forward<T>(value));
        } else {
            using Result = remove_cvref_t<
                std::invoke_result_t<F, const typename Impl::element_type &>>;
            // Non-capturing marker, matching the declaration's second
            // alternative: a lambda inside a requires-expression that
            // captures a local (here, `function`) is accepted by GCC but
            // rejected by the Clang front end the wording generator uses
            // ("variable cannot be implicitly captured" / "reference to
            // local variable declared in enclosing function"). This
            // static_assert is provable redundant given the declaration's
            // constraint already selected this branch -- it is the
            // GHC-MINIMAL-style last-resort message, not load-bearing SFINAE
            // -- so the marker shape is exactly as informative.
            static_assert(
                requires {
                    impl_of(self).fold_right(
                        std::forward<T>(value), monoid_identity<Result>(),
                        [](const auto &, Result acc) { return acc; });
                }, "Foldable Impl must provide at least one basis: "
                   "fold_map(f, container), or fold_right(container, state, f) "
                   "plus element_type.");
            return impl_of(self).fold_right(
                std::forward<T>(value), monoid_identity<Result>(),
                [&function](const auto &elem, Result acc) {
                    return monoid_combine(std::invoke(function, elem),
                                          std::move(acc));
                });
        }
    }

    /** Returns the number of elements in the foldable container. */
    template <class T>
    auto length(this auto &&self, T &&value) -> std::size_t
        requires requires(const Impl &impl) {
            impl.length(std::forward<T>(value));
        } || requires {
            // self, not impl: fold_map is itself now a probing member with
            // its own either-basis constraint, so checking availability
            // through self is what correctly admits a fold_right +
            // element_type Impl. Checking impl.fold_map directly would
            // reject that Impl, since it has no fold_map member at all.
            self.fold_map([](const auto &) { return Count{1}; },
                          std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).length(std::forward<T>(value));
                      }) {
            return impl_of(self).length(std::forward<T>(value));
        } else {
            const auto count = self.fold_map(
                [](const auto &) { return Count{1}; }, std::forward<T>(value));
            return count.d_value;
        }
    }

    /** Left-associative fold: applies `function(state, element)` for each
     * element in traversal order, starting from `initial_state`.
     */
    template <class T, class STATE, class F>
    auto fold_left(this auto &&self, T &&value, STATE initial_state,
                   F &&function)
        requires requires(const Impl &impl) {
            impl.fold_left(std::forward<T>(value), initial_state,
                           std::forward<F>(function));
        } || requires {
            // self, not impl -- see length's second alternative. Also a
            // non-capturing marker: fold_map is generic in its callable, so
            // only the return-type shape (LeftFoldProgram<StateType>)
            // matters for the probe. A capturing lambda naming `function`
            // here would reference a function parameter from inside a
            // trailing requires-clause's lambda, which GCC rejects
            // (-Wtemplate-body, "use of parameter outside function body").
            self.fold_map(
                [](const auto &)
                    -> detail::LeftFoldProgram<remove_cvref_t<STATE>> {
                    return {};
                },
                std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).fold_left(std::forward<T>(value),
                                                  initial_state,
                                                  std::forward<F>(function));
                      }) {
            return impl_of(self).fold_left(std::forward<T>(value),
                                           std::move(initial_state),
                                           std::forward<F>(function));
        } else {
            using StateType = remove_cvref_t<STATE>;
            auto step = std::forward<F>(function);

            const auto program = self.fold_map(
                [&step](const auto &x) {
                    using ValueType = remove_cvref_t<decltype(x)>;
                    return detail::LeftFoldProgram<StateType>{
                        [x_copy = ValueType(x), &step](StateType s) {
                            return std::invoke(step, std::move(s), x_copy);
                        }};
                },
                std::forward<T>(value));

            return program(StateType(std::move(initial_state)));
        }
    }

    /** Right-associative fold: applies `function(element, state)` for each
     * element in reverse traversal order, starting from `initial_state`.
     */
    template <class T, class STATE, class F>
    auto fold_right(this auto &&self, T &&value, STATE initial_state,
                    F &&function)
        requires requires(const Impl &impl) {
            impl.fold_right(std::forward<T>(value), initial_state,
                            std::forward<F>(function));
        } || requires(const Impl &impl) {
            impl.fold_map(
                [](const auto &)
                    -> detail::RightFoldProgram<remove_cvref_t<STATE>> {
                    return {};
                },
                std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).fold_right(std::forward<T>(value),
                                                   initial_state,
                                                   std::forward<F>(function));
                      }) {
            return impl_of(self).fold_right(std::forward<T>(value),
                                            std::move(initial_state),
                                            std::forward<F>(function));
        } else {
            using StateType = remove_cvref_t<STATE>;
            auto step = std::forward<F>(function);

            // Non-capturing marker; see fold_map's static_assert for why.
            static_assert(
                requires {
                    impl_of(self).fold_map(
                        [](const auto &)
                            -> detail::RightFoldProgram<StateType> {
                            return {};
                        },
                        std::forward<T>(value));
                }, "Foldable Impl must provide at least one basis: "
                   "fold_map(f, container), or fold_right(container, state, f) "
                   "plus element_type.");
            const auto program = impl_of(self).fold_map(
                [&step](const auto &x) {
                    using ValueType = remove_cvref_t<decltype(x)>;
                    return detail::RightFoldProgram<StateType>{
                        [x_copy = ValueType(x), &step](StateType s) {
                            return std::invoke(step, x_copy, std::move(s));
                        }};
                },
                std::forward<T>(value));

            return program(StateType(std::move(initial_state)));
        }
    }

    /** Combines all elements using the Monoid of the element type
     * (requires elements themselves to be Monoid values).
     */
    template <class T>
    auto combine_all(this auto &&self, T &&value)
        requires requires(const Impl &impl) {
            impl.combine_all(std::forward<T>(value));
        } || requires {
            // self, not impl -- see length's second alternative.
            self.fold_map([](const auto & x) { return x; },
                          std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).combine_all(std::forward<T>(value));
                      }) {
            return impl_of(self).combine_all(std::forward<T>(value));
        } else {
            return self.fold_map([](const auto &x) { return x; },
                                 std::forward<T>(value));
        }
    }

    /** Alias for `combine_all`. Its second alternative names what it
     * actually calls -- self.combine_all, which is itself a probing member
     * -- rather than fold_map. Naming fold_map here would reject an Impl
     * that provides a native combine_all directly but no fold_map at all.
     */
    template <class T>
    auto fold(this auto &&self, T &&value)
        requires requires(const Impl &impl) {
            impl.fold(std::forward<T>(value));
        } || requires { self.combine_all(std::forward<T>(value)); }
    {
        if constexpr (requires {
                          impl_of(self).fold(std::forward<T>(value));
                      }) {
            return impl_of(self).fold(std::forward<T>(value));
        } else {
            return self.combine_all(std::forward<T>(value));
        }
    }

    /** Returns `true` if any element satisfies `predicate`. */
    template <class T, class PREDICATE>
    auto any_of(this auto &&self, T &&value, PREDICATE &&predicate) -> bool
        requires requires(const Impl &impl) {
            impl.any_of(std::forward<T>(value),
                        std::forward<PREDICATE>(predicate));
        } || requires {
            // self, not impl -- see length's second alternative. Also a
            // non-capturing marker: only the Any-shaped return matters for
            // the probe, and capturing `predicate` here would reference a
            // function parameter from inside a trailing requires-clause's
            // lambda, which GCC rejects.
            self.fold_map([](const auto &) { return Any{true}; },
                          std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).any_of(
                              std::forward<T>(value),
                              std::forward<PREDICATE>(predicate));
                      }) {
            return impl_of(self).any_of(std::forward<T>(value),
                                        std::forward<PREDICATE>(predicate));
        } else {
            const auto result = self.fold_map(
                [&predicate](const auto &x) {
                    return Any{std::invoke(predicate, x)};
                },
                std::forward<T>(value));

            return result.d_value;
        }
    }

    /** Returns `true` if all elements satisfy `predicate`. */
    template <class T, class PREDICATE>
    auto all_of(this auto &&self, T &&value, PREDICATE &&predicate) -> bool
        requires requires(const Impl &impl) {
            impl.all_of(std::forward<T>(value),
                        std::forward<PREDICATE>(predicate));
        } || requires {
            // self, not impl; see any_of's second alternative.
            self.fold_map([](const auto &) { return All{true}; },
                          std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).all_of(
                              std::forward<T>(value),
                              std::forward<PREDICATE>(predicate));
                      }) {
            return impl_of(self).all_of(std::forward<T>(value),
                                        std::forward<PREDICATE>(predicate));
        } else {
            const auto result = self.fold_map(
                [&predicate](const auto &x) {
                    return All{std::invoke(predicate, x)};
                },
                std::forward<T>(value));

            return result.d_value;
        }
    }

    /** Returns `true` if the container holds no elements. Its second
     * alternative names self.any_of for the same reason `fold`'s names
     * self.combine_all: an Impl may provide a native any_of directly, with
     * no fold_map at all.
     */
    template <class T>
    auto empty(this auto &&self, T &&value) -> bool
        requires requires(const Impl &impl) {
            impl.empty(std::forward<T>(value));
        } || requires {
            self.any_of(std::forward<T>(value),
                        [](const auto &) { return true; });
        }
    {
        if constexpr (requires {
                          impl_of(self).empty(std::forward<T>(value));
                      }) {
            return impl_of(self).empty(std::forward<T>(value));
        } else {
            return !self.any_of(std::forward<T>(value),
                                [](const auto &) { return true; });
        }
    }

    /** Collects all elements into a `std::vector` in traversal order. */
    template <class T>
    auto to_vector(this auto &&self, T &&value)
        requires requires(const Impl &impl) {
            impl.to_vector(std::forward<T>(value));
        } || requires {
            // self, not impl -- see length's second alternative.
            self.fold_map(
                [](const auto & x) {
                    using ValueType = remove_cvref_t<decltype(x)>;
                    return std::vector<ValueType>{x};
                },
                std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).to_vector(std::forward<T>(value));
                      }) {
            return impl_of(self).to_vector(std::forward<T>(value));
        } else {
            return self.fold_map(
                [](const auto &x) {
                    using ValueType = remove_cvref_t<decltype(x)>;
                    return std::vector<ValueType>{x};
                },
                std::forward<T>(value));
        }
    }

    /** Returns the first element satisfying `predicate`, or an empty optional.
     */
    template <class T, class PREDICATE>
    auto find_first(this auto &&self, T &&value, PREDICATE &&predicate)
        requires requires(const Impl &impl) {
            impl.find_first(std::forward<T>(value),
                            std::forward<PREDICATE>(predicate));
        } || requires {
            // self, not impl; see any_of's second alternative.
            self.fold_map(
                [](const auto &
                   x) -> detail::First<remove_cvref_t<decltype(x)>> {
                    return {};
                },
                std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).find_first(
                              std::forward<T>(value),
                              std::forward<PREDICATE>(predicate));
                      }) {
            return impl_of(self).find_first(std::forward<T>(value),
                                            std::forward<PREDICATE>(predicate));
        } else {
            const auto result = self.fold_map(
                [&predicate](const auto &x) {
                    using X = remove_cvref_t<decltype(x)>;
                    if (std::invoke(predicate, x)) {
                        return detail::First<X>{{x}};
                    }
                    return detail::First<X>{{}};
                },
                std::forward<T>(value));

            return result.d_value;
        }
    }

  private:
    //! \omit
    template <class SELF>
    static constexpr decltype(auto) impl_of(SELF &&self) {
        return static_cast<impl_ref_t<Impl, SELF>>(self);
    }
};

/** Typeclass lookup variable for Foldable; specialize for each container type.
 */
template <class T>
inline constexpr auto foldable_typeclass = std::false_type{};

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_FOLD_HPP
