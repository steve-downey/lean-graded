// include/beman/transpose/functor.hpp                                -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_FUNCTOR_HPP
#define BEMAN_TRANSPOSE_FUNCTOR_HPP

#include <beman/transpose/detail/typeclass_base.hpp>

#include <algorithm>
#include <concepts>
#include <functional>
#include <iterator>
#include <optional>
#include <type_traits>
#include <utility>
#include <vector>

namespace beman::transpose {

// Functor pattern invariants:
// - Instances are single lookup objects that provide fmap(F, T).
// - replace is a derived object operation implemented from fmap.
// - Dispatch happens through a provided object or functor_typeclass<Concrete>.
// - Keep lookup explicit through typeclass objects, not ADL overloads.

/** CRTP base for Functor instances.
 * `Impl` must provide `fmap(f, container)`; `replace` is derived from it.
 */
template <class Impl>
struct Functor : protected Impl {
    /** Applies `function` to every element of `value`. */
    template <class FUNCTION, class T>
    auto fmap(this auto &&self, FUNCTION &&function, T &&value)
        requires requires(const Impl &impl) {
            impl.fmap(std::forward<FUNCTION>(function), std::forward<T>(value));
        }
    {
        return impl_of(self).fmap(std::forward<FUNCTION>(function),
                                  std::forward<T>(value));
    }

    /** Replaces every element of `value` with `replacement`, ignoring the
     * original element values. Prefers a native `Impl::replace` when the
     * instance supplies one.
     */
    template <class T, class U>
    auto replace(this auto &&self, T &&value, U &&replacement)
        requires requires(const Impl &impl) {
            impl.replace(std::forward<T>(value), std::forward<U>(replacement));
        } || requires(const Impl &impl) {
            impl.fmap([replacement = std::forward<U>(replacement)](
                          const auto &) { return replacement; },
                      std::forward<T>(value));
        }
    {
        if constexpr (requires {
                          impl_of(self).replace(std::forward<T>(value),
                                                std::forward<U>(replacement));
                      }) {
            return impl_of(self).replace(std::forward<T>(value),
                                         std::forward<U>(replacement));
        } else {
            // One-way derivation (not a mutually-derivable pair): route
            // through self, not Impl, so a shadow on a wrapping Map is
            // still reached.
            return self.fmap([replacement = std::forward<U>(replacement)](
                                 const auto &) { return replacement; },
                             std::forward<T>(value));
        }
    }

  private:
    //! \omit
    template <class SELF>
    static constexpr decltype(auto) impl_of(SELF &&self) {
        return static_cast<impl_ref_t<Impl, SELF>>(self);
    }
};

/** Typeclass lookup variable for Functor; specialize for each container type.
 */
template <class T>
inline constexpr auto functor_typeclass = std::false_type{};

/** Restricted `Impl` concept for Functor: satisfied when `IMPL` supplies the
 * minimal complete basis the `Functor` CRTP base needs -- `fmap` alone,
 * probed with a representative witness callable. This is the `MINIMAL`
 * pragma to `functor_object`'s class declaration: an `IMPL` may satisfy
 * this concept and still fail `functor_object`, which is exactly the
 * bargain the CRTP base exists to keep. Never demand a derived operation
 * (`replace`) here; that surface belongs to `functor_object` alone.
 */
template <class IMPL, class CONTEXT>
concept functor_impl = requires(const IMPL &impl, const CONTEXT &context) {
    impl.fmap(detail::probe_witness<applicative_value_t<CONTEXT>>{}, context);
};

/** Deep object concept for a Functor object over `CONTEXT`: satisfied when
 * `OBJ` provides the full object surface -- `fmap` (probed with a
 * representative witness callable, not a proof for every callable) and the
 * derived `replace`. Conformance here is structural, so a hand-implemented
 * object that never uses the `Functor` CRTP base can satisfy this concept
 * too; nothing here requires deriving from `Functor<Impl>`.
 *
 * There is no superclass edge to `Applicative` or `Monad`. In particular, a
 * bare `Monad` object correctly fails this concept: `Monad<Impl>` grows only
 * the Functor basis (`fmap`), never the derived surface, so it has no
 * `replace`. Wrapping the monad object in `Functor<>` (`Functor<SomeMonadMap>`)
 * is today's remedy; a later presentation member on `Monad` is expected to
 * name the same wrapping.
 */
template <class OBJ, class CONTEXT>
concept functor_object = requires(const OBJ &obj, const CONTEXT &context,
                                  const applicative_value_t<CONTEXT> &element) {
    obj.fmap(detail::probe_witness<applicative_value_t<CONTEXT>>{}, context);
    obj.replace(context, element);
};

template <class VALUE_TYPE>
struct OptionalFunctorImpl {
    template <class F>
    auto fmap(this auto &&, F &&function,
              const std::optional<VALUE_TYPE> &value) {
        using Result = std::invoke_result_t<F, const VALUE_TYPE &>;
        if (!value) {
            return std::optional<remove_cvref_t<Result>>{};
        }
        return std::optional<remove_cvref_t<Result>>{
            std::invoke(std::forward<F>(function), *value)};
    }
};

template <class VALUE_TYPE>
struct VectorFunctorImpl {
    template <class F>
    auto fmap(this auto &&, F &&function,
              const std::vector<VALUE_TYPE> &values) {
        using Result = std::invoke_result_t<F, const VALUE_TYPE &>;
        std::vector<remove_cvref_t<Result>> output;
        output.reserve(values.size());

        std::ranges::transform(values, std::back_inserter(output),
                               [&function](const VALUE_TYPE &v) {
                                   return std::invoke(function, v);
                               });

        return output;
    }
};

template <class VALUE_TYPE>
struct OptionalFunctorMap : Functor<OptionalFunctorImpl<VALUE_TYPE>> {
    using OptionalFunctorImpl<VALUE_TYPE>::fmap;
};

template <class VALUE_TYPE>
struct VectorFunctorMap : Functor<VectorFunctorImpl<VALUE_TYPE>> {
    using VectorFunctorImpl<VALUE_TYPE>::fmap;
};

/** Functor instance for `std::optional<VALUE_TYPE>`. */
template <class VALUE_TYPE>
inline constexpr auto functor_typeclass<std::optional<VALUE_TYPE>> =
    OptionalFunctorMap<VALUE_TYPE>{};

/** Functor instance for `std::vector<VALUE_TYPE>`. */
template <class VALUE_TYPE>
inline constexpr auto functor_typeclass<std::vector<VALUE_TYPE>> =
    VectorFunctorMap<VALUE_TYPE>{};

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_FUNCTOR_HPP
