// include/beman/transpose/apply.hpp                                  -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_APPLY_HPP
#define BEMAN_TRANSPOSE_APPLY_HPP

#include <beman/transpose/detail/applicative_derivation.hpp>
#include <beman/transpose/detail/typeclass_base.hpp>
#include <beman/transpose/grade.hpp>

#include <concepts>
#include <functional>
#include <optional>
#include <tuple>
#include <type_traits>
#include <utility>

namespace beman::transpose {

/// Namespace-scope spelling of the evaluator named by `ap`'s constraint. A
/// second object of the `detail` type, not a reference to it: the type is
/// empty and stateless, so the two are interchangeable, and a reference's
/// declared type does not currently survive `\seebelow` masking
/// (steve-downey/specgen#33). It exists so that a declaration the
/// specification shows does not carry an implementation namespace qualifier
/// into the wording.
//! \seebelow
//! \remarks `applicative_eval` applies a callable to one argument. It is the
//! evaluator that recovers one-step application from the n-ary core:
//! `ap(f, x)` is `invoke(applicative_eval, f, x)`. Naming it is what makes
//! `ap`'s second alternative expressible, and that alternative is satisfied
//! only where the context can hold a callable.
inline constexpr detail::applicative_eval_t applicative_eval{};

namespace detail {

// A generic lambda-expression is a distinct, unrelated type at every
// occurrence in the source, so it cannot be the shared expression a
// disjunctive requires-clause needs at both the in-class declaration and
// the out-of-line definition (they must be spelled with the same tokens
// naming the same entity). discard_first_eval_t and discard_second_eval_t
// give `discard_first` and `discard_second` a named, stable callable for
// that purpose -- the same role applicative_eval_t plays for `ap`.

//! \omit
struct discard_first_eval_t {
    template <class FIRST, class SECOND>
    constexpr auto operator()(const FIRST &, SECOND &&second) const
        -> SECOND && {
        return std::forward<SECOND>(second);
    }
};

//! \omit
struct discard_second_eval_t {
    template <class FIRST, class SECOND>
    constexpr auto operator()(FIRST &&first, const SECOND &) const -> FIRST && {
        return std::forward<FIRST>(first);
    }
};

} // namespace detail

/// Namespace-scope spelling of the evaluator named by `discard_first`'s
/// constraint, for the same reason `applicative_eval` is named rather than
/// spelled inline: a lambda-expression cannot be repeated identically
/// between an in-class declaration and its out-of-line definition.
//! \seebelow
//! \remarks `discard_first_eval` discards its first argument and returns
//! its second. It is the evaluator `discard_first`'s second alternative
//! probes, and that alternative is satisfied exactly when `discard_first`'s
//! own `invoke`-based derivation would be.
inline constexpr detail::discard_first_eval_t discard_first_eval{};

/// Namespace-scope spelling of the evaluator named by `discard_second`'s
/// constraint; see `discard_first_eval` above.
//! \seebelow
//! \remarks `discard_second_eval` discards its second argument and returns
//! its first. It is the evaluator `discard_second`'s second alternative
//! probes, and that alternative is satisfied exactly when `discard_second`'s
//! own `invoke`-based derivation would be.
inline constexpr detail::discard_second_eval_t discard_second_eval{};

/// Applicative pattern invariants:
/// - Dual BASIS, single INTERFACE. An instance opts in with pure + invoke
///   or pure + ap -- both are perfectly cromulent bases, and the base class
///   derives whichever one the instance does not supply. The user-facing
///   application verb is invoke: McBride & Paterson's canonical form
///     pure f <*> u1 <*> ... <*> un   ==   invoke(f, u1, ..., un),
///   and the GHC analogue is {-# MINIMAL pure, ((<*>) | liftA2) #-}.
/// - ap (one-step application of a callable-in-context) is the classic
///   basis and remains available as a secondary operation, but it is never
///   the lead verb: papers, examples, and teaching lead with invoke. The
///   interface choice is forced by std::simd::vec, which cannot form a
///   vec<callable> -- ap is unspellable exactly where this proposal's
///   motivation lives, while n-ary invoke works everywhere.
/// - ap-from-invoke is invoke(applicative_eval, cf, cx); it exists only
///   when the context can hold a callable. invoke-from-ap is the currying
///   derivation (detail::terminating_partial); its cost lives entirely in
///   the derivation direction.
/// - Impls keep their basis SFINAE-friendly: a trailing return type via
///   std::invoke_result_t (or an explicit requires clause), never a bare
///   auto return with the result type computed only in the body, so that
///   availability probes fail cleanly instead of hard-erroring.
/// - Derived operations (map/lift/zip_with/discard_*) live on that object.
/// - Dispatch happens through a provided object or
///   applicative_typeclass<Concrete>.
/// - Do not introduce hidden alternate semantics without a distinct map/type.
/// CRTP base for Applicative instances.
/// `Impl` must provide `pure(value)` and either the n-ary
/// `invoke(f, args_in_context...)` or the one-step
/// `ap(f_in_context, arg_in_context)`; the base derives the missing one and
/// every other operation. invoke is the user-facing interface; ap is the
/// classic basis.
template <class Impl>
struct Applicative : protected Impl {
    static_assert(
        !std::is_same_v<Impl, std::false_type>,
        "No applicative_typeclass<T> specialization found. "
        "Specialize beman::transpose::applicative_typeclass<T> for "
        "your type T and provide pure(...) plus invoke(...) or ap(...).");
    using Impl::pure;

    // \ref{transpose.applicative.basis}, basis operations
    template <class FUNCTION, class FIRST_ARGUMENT, class... REST_ARGUMENTS>
    auto invoke(this auto &&self, FUNCTION &&function,
                FIRST_ARGUMENT &&first_argument,
                REST_ARGUMENTS &&...rest_arguments);

    template <class FUNCTION_IN_CONTEXT, class ARGUMENT_IN_CONTEXT>
    auto ap(this auto &&self, FUNCTION_IN_CONTEXT &&function,
            ARGUMENT_IN_CONTEXT &&argument)
        requires requires(const Impl &impl) {
            impl.ap(std::forward<FUNCTION_IN_CONTEXT>(function),
                    std::forward<ARGUMENT_IN_CONTEXT>(argument));
        } || requires(const Impl &impl) {
            impl.invoke(applicative_eval,
                        std::forward<FUNCTION_IN_CONTEXT>(function),
                        std::forward<ARGUMENT_IN_CONTEXT>(argument));
        };

    // \ref{transpose.applicative.derived}, derived operations
    template <class FUNCTION, class ARGUMENT>
    auto map(this auto &&self, FUNCTION &&function, ARGUMENT &&argument)
        requires requires(const Impl &impl) {
            impl.map(std::forward<FUNCTION>(function),
                     std::forward<ARGUMENT>(argument));
        } || requires {
            self.invoke(std::forward<FUNCTION>(function),
                        std::forward<ARGUMENT>(argument));
        };

    template <class VALUE>
    auto lift(this auto &&self, VALUE &&value)
        requires requires(const Impl &impl) {
            impl.lift(std::forward<VALUE>(value));
        } || requires { self.pure(std::forward<VALUE>(value)); };

    template <class FUNCTION, class FIRST_ARGUMENT, class SECOND_ARGUMENT>
    auto zip_with(this auto &&self, FUNCTION &&function,
                  FIRST_ARGUMENT &&first_argument,
                  SECOND_ARGUMENT &&second_argument)
        requires requires(const Impl &impl) {
            impl.zip_with(std::forward<FUNCTION>(function),
                          std::forward<FIRST_ARGUMENT>(first_argument),
                          std::forward<SECOND_ARGUMENT>(second_argument));
        } || requires {
            self.invoke(std::forward<FUNCTION>(function),
                        std::forward<FIRST_ARGUMENT>(first_argument),
                        std::forward<SECOND_ARGUMENT>(second_argument));
        };

    template <class FIRST_ARGUMENT, class SECOND_ARGUMENT>
    auto discard_first(this auto &&self, FIRST_ARGUMENT &&first_argument,
                       SECOND_ARGUMENT &&second_argument)
        requires requires(const Impl &impl) {
            impl.discard_first(std::forward<FIRST_ARGUMENT>(first_argument),
                               std::forward<SECOND_ARGUMENT>(second_argument));
        } || requires {
            self.invoke(discard_first_eval,
                        std::forward<FIRST_ARGUMENT>(first_argument),
                        std::forward<SECOND_ARGUMENT>(second_argument));
        };

    template <class FIRST_ARGUMENT, class SECOND_ARGUMENT>
    auto discard_second(this auto &&self, FIRST_ARGUMENT &&first_argument,
                        SECOND_ARGUMENT &&second_argument)
        requires requires(const Impl &impl) {
            impl.discard_second(std::forward<FIRST_ARGUMENT>(first_argument),
                                std::forward<SECOND_ARGUMENT>(second_argument));
        } || requires {
            self.invoke(discard_second_eval,
                        std::forward<FIRST_ARGUMENT>(first_argument),
                        std::forward<SECOND_ARGUMENT>(second_argument));
        };

    // \ref{transpose.applicative.grade}, grade re-indexing
    template <class TARGET_GRADE, class CARRIER>
    constexpr auto subsume(this auto &&, CARRIER &&value)
        requires requires {
            grade_subsume<TARGET_GRADE>(std::forward<CARRIER>(value));
        };

    // \ref{transpose.applicative.delegate}, delegated application
    template <class APPLICATIVE_MAP, class FUNCTION, class FIRST_ARGUMENT,
              class... REST_ARGUMENTS>
    auto invoke_with(this auto &&, const APPLICATIVE_MAP &applicative_map,
                     FUNCTION &&function, FIRST_ARGUMENT &&first_argument,
                     REST_ARGUMENTS &&...rest_arguments);

    template <const auto &APPLICATIVE_MAP, class FUNCTION, class FIRST_ARGUMENT,
              class... REST_ARGUMENTS>
    auto invoke_with(this auto &&, FUNCTION &&function,
                     FIRST_ARGUMENT &&first_argument,
                     REST_ARGUMENTS &&...rest_arguments);

  private:
    //! \omit
    template <class SELF>
    static constexpr decltype(auto) impl_of(SELF &&self) {
        return static_cast<impl_ref_t<Impl, SELF>>(self);
    }

    //! \omit
    template <class ACCUMULATED>
    auto ap_chain(this auto &&, ACCUMULATED &&accumulated) {
        return std::forward<ACCUMULATED>(accumulated);
    }

    //! \omit
    template <class ACCUMULATED, class NEXT_ARGUMENT, class... REST_ARGUMENTS>
    auto ap_chain(this auto &&self, ACCUMULATED &&accumulated,
                  NEXT_ARGUMENT &&next_argument,
                  REST_ARGUMENTS &&...rest_arguments) {
        auto next = self.ap(std::forward<ACCUMULATED>(accumulated),
                            std::forward<NEXT_ARGUMENT>(next_argument));
        if constexpr (sizeof...(REST_ARGUMENTS) == 0) {
            return next;
        } else {
            return self.ap_chain(std::move(next), std::forward<REST_ARGUMENTS>(
                                                      rest_arguments)...);
        }
    }
};

//! \remarks This variable template is the lookup point for the Applicative
//! object of a context type. A program may specialize it for a
//! program-defined context. The primary template names no applicative
//! object.
template <class T>
inline constexpr auto applicative_typeclass = std::false_type{};

//! \remarks This variable template is a second lookup point, over the same
//! carrier and grade algebra as `applicative_typeclass`, naming the
//! accumulating Applicative object. Where the object named by
//! `applicative_typeclass` stops at the first failing operand, this object
//! combines the evidence of every failing operand. Neither object is
//! selected automatically for a carrier: the context type alone does not
//! determine which composition discipline a caller wants. This object has
//! no Monad instance, because sequencing requires a value from a
//! computation that accumulation admits may have failed.
template <class T>
inline constexpr auto accumulating_applicative_typeclass = std::false_type{};

//! \remarks This concept is satisfied when `OBJ` provides the full
//! Applicative object surface over `CONTEXT`: `pure`, the `invoke` basis, and
//! the derived `map`, `lift`, `zip_with`, `discard_first`, `discard_second`
//! and `invoke_with`. `ap` and `subsume` are required only where their own
//! condition -- the same one their own declarations carry, not a second
//! spelling of it -- licenses them: `ap` where `CONTEXT` can hold a
//! callable (probed by lifting a witness callable through `OBJ`'s own
//! `pure`, the same mechanism the library's own ap-from-invoke derivation
//! uses), `subsume` where `CONTEXT` participates in grading. Operations
//! templated over an arbitrary callable are probed with one representative
//! witness (`probe_witness`/`probe_witness2`): this checks that the
//! operation exists, not that it holds for every callable. Conformance here
//! is structural, so a hand-implemented object that never derives from
//! `Applicative<Impl>` can satisfy this concept.
template <class OBJ, class CONTEXT>
concept applicative_object =
    requires(const OBJ &obj, const CONTEXT &context,
             const applicative_value_t<CONTEXT> &element) {
        obj.pure(element);
        obj.invoke(probe_witness<applicative_value_t<CONTEXT>>{}, context);
        obj.map(probe_witness<applicative_value_t<CONTEXT>>{}, context);
        obj.lift(element);
        obj.zip_with(probe_witness2<applicative_value_t<CONTEXT>>{}, context,
                     context);
        obj.discard_first(context, context);
        obj.discard_second(context, context);
        obj.invoke_with(obj, probe_witness<applicative_value_t<CONTEXT>>{},
                        context);
    } &&
    (!requires(const OBJ &obj) {
        obj.pure(probe_witness<applicative_value_t<CONTEXT>>{});
    } || requires(const OBJ &obj, const CONTEXT &context) {
        obj.ap(obj.pure(probe_witness<applicative_value_t<CONTEXT>>{}),
               context);
    }) &&
    (!graded_context<CONTEXT> ||
     requires(const OBJ &obj, const CONTEXT &context) {
         obj.template subsume<grade_of_t<CONTEXT>>(context);
     });

/// Applicative instance for std::optional: the flagship of the invoke core.
/// The trailing return type keeps invoke SFINAE-friendly so availability
/// probes fail cleanly.
template <class VALUE_TYPE>
struct OptionalApplicativeImpl {
    // \ref{transpose.applicative.optional}, applicative instance for optional
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value)
        -> std::optional<remove_cvref_t<VALUE>>;

    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function,
                const std::optional<FIRST> &first,
                const std::optional<REST> &...rest)
        -> std::optional<remove_cvref_t<
            std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>>;
};

template <class VALUE_TYPE>
struct OptionalApplicativeMap
    : Applicative<OptionalApplicativeImpl<VALUE_TYPE>> {
    using OptionalApplicativeImpl<VALUE_TYPE>::invoke;
    using OptionalApplicativeImpl<VALUE_TYPE>::pure;
};

/// Applicative instance for `std::optional<VALUE_TYPE>`.
template <class VALUE_TYPE>
inline constexpr auto applicative_typeclass<std::optional<VALUE_TYPE>> =
    OptionalApplicativeMap<VALUE_TYPE>{};

// \rSec3[transpose.applicative.basis]{Basis operations}

//! \constraints `Impl` provides either an `invoke` accepting `function` and
//! the arguments, or an `ap` accepting a callable in context and one
//! argument in context.
//! \effects Lifts `function` into the context and applies it to the
//! arguments, left to right. If `Impl` provides `invoke`, the effect is that
//! of `Impl`'s own `invoke`; otherwise `function` is embedded with `pure` and
//! applied one argument at a time using `ap`.
//! \returns The single value in context holding the result of applying
//! `function` to the values held by the arguments.
//! \remarks The arguments are evaluated in the order written. No argument's
//! context depends on another argument's value.
template <class Impl>
template <class FUNCTION, class FIRST_ARGUMENT, class... REST_ARGUMENTS>
auto Applicative<Impl>::invoke(this auto &&self, FUNCTION &&function,
                               FIRST_ARGUMENT &&first_argument,
                               REST_ARGUMENTS &&...rest_arguments) {
    if constexpr (requires {
                      impl_of(self).invoke(
                          std::forward<FUNCTION>(function),
                          std::forward<FIRST_ARGUMENT>(first_argument),
                          std::forward<REST_ARGUMENTS>(rest_arguments)...);
                  }) {
        return impl_of(self).invoke(
            std::forward<FUNCTION>(function),
            std::forward<FIRST_ARGUMENT>(first_argument),
            std::forward<REST_ARGUMENTS>(rest_arguments)...);
    } else {
        // Derivation from the ap basis:
        //   invoke(f, x1, ..., xn) = pure(curried f) `ap` x1 `ap` ... xn
        auto lifted_function = self.pure(
            detail::make_terminating_partial(std::forward<FUNCTION>(function)));
        static_assert(
            requires {
                impl_of(self).ap(std::move(lifted_function),
                                 std::forward<FIRST_ARGUMENT>(first_argument));
            }, "Applicative Impl must provide pure and at least one basis: "
               "invoke(f, args_in_context...) or "
               "ap(f_in_context, arg_in_context).");
        return self.ap_chain(
            self.ap(std::move(lifted_function),
                    std::forward<FIRST_ARGUMENT>(first_argument)),
            std::forward<REST_ARGUMENTS>(rest_arguments)...);
    }
}

//! \constraints `Impl` provides either an `ap` accepting `function` and
//! `argument`, or an `invoke` able to apply a callable held in the context to
//! one argument in the context. The second alternative is satisfied only
//! where the context can hold a callable, so `ap` does not participate in
//! overload resolution for a context that cannot.
//! \effects Applies the callable held by `function` to the value held by
//! `argument`. If `Impl` provides `ap`, the effect is that of `Impl`'s own
//! `ap`; otherwise the application is expressed through `Impl`'s `invoke`.
//! \returns The single value in context holding the result of that
//! application.
//! \remarks This is the classic one-step application, retained as a secondary
//! operation and as an instance basis. Both alternatives address `Impl`
//! directly, so no derivation cycle with `invoke` arises.
template <class Impl>
template <class FUNCTION_IN_CONTEXT, class ARGUMENT_IN_CONTEXT>
auto Applicative<Impl>::ap(this auto &&self, FUNCTION_IN_CONTEXT &&function,
                           ARGUMENT_IN_CONTEXT &&argument)
    requires requires(const Impl &impl) {
        impl.ap(std::forward<FUNCTION_IN_CONTEXT>(function),
                std::forward<ARGUMENT_IN_CONTEXT>(argument));
    } || requires(const Impl &impl) {
        impl.invoke(applicative_eval,
                    std::forward<FUNCTION_IN_CONTEXT>(function),
                    std::forward<ARGUMENT_IN_CONTEXT>(argument));
    }
{
    if constexpr (requires {
                      impl_of(self).ap(
                          std::forward<FUNCTION_IN_CONTEXT>(function),
                          std::forward<ARGUMENT_IN_CONTEXT>(argument));
                  }) {
        return impl_of(self).ap(std::forward<FUNCTION_IN_CONTEXT>(function),
                                std::forward<ARGUMENT_IN_CONTEXT>(argument));
    } else {
        return impl_of(self).invoke(
            detail::applicative_eval,
            std::forward<FUNCTION_IN_CONTEXT>(function),
            std::forward<ARGUMENT_IN_CONTEXT>(argument));
    }
}

// \rSec3[transpose.applicative.derived]{Derived operations}

//! \constraints `Impl` provides either a `map` accepting `function` and
//! `argument`, or an `invoke` accepting `function` and `argument`, whether
//! native to `Impl` or derived from `Impl`'s basis.
//! \effects If `Impl` provides `map`, the effect is that of `Impl`'s own
//! `map`; otherwise the application is expressed through the object's own
//! `invoke`, available for either half of the dual basis.
//! \returns The single value in context holding the result of applying
//! `function` to the value held by `argument`.
template <class Impl>
template <class FUNCTION, class ARGUMENT>
auto Applicative<Impl>::map(this auto &&self, FUNCTION &&function,
                            ARGUMENT &&argument)
    requires requires(const Impl &impl) {
        impl.map(std::forward<FUNCTION>(function),
                 std::forward<ARGUMENT>(argument));
    } || requires {
        self.invoke(std::forward<FUNCTION>(function),
                    std::forward<ARGUMENT>(argument));
    }
{
    if constexpr (requires {
                      impl_of(self).map(std::forward<FUNCTION>(function),
                                        std::forward<ARGUMENT>(argument));
                  }) {
        return impl_of(self).map(std::forward<FUNCTION>(function),
                                 std::forward<ARGUMENT>(argument));
    } else {
        return self.invoke(std::forward<FUNCTION>(function),
                           std::forward<ARGUMENT>(argument));
    }
}

//! \constraints `Impl` provides either a `lift` accepting `value`, or a
//! `pure` accepting `value`.
//! \effects If `Impl` provides `lift`, the effect is that of `Impl`'s own
//! `lift`; otherwise `value` is lifted into the context using the object's
//! own `pure`, which `Impl` is required to provide directly.
//! \returns The single value in context holding `value`.
template <class Impl>
template <class VALUE>
auto Applicative<Impl>::lift(this auto &&self, VALUE &&value)
    requires requires(const Impl &impl) {
        impl.lift(std::forward<VALUE>(value));
    } || requires { self.pure(std::forward<VALUE>(value)); }
{
    if constexpr (requires {
                      impl_of(self).lift(std::forward<VALUE>(value));
                  }) {
        return impl_of(self).lift(std::forward<VALUE>(value));
    } else {
        return self.pure(std::forward<VALUE>(value));
    }
}

//! \constraints `Impl` provides either a `zip_with` accepting `function` and
//! the two arguments, or an `invoke` accepting `function` and the two
//! arguments, whether native to `Impl` or derived from `Impl`'s basis.
//! \effects If `Impl` provides `zip_with`, the effect is that of `Impl`'s
//! own `zip_with`; otherwise the application is expressed through the
//! object's own `invoke`, available for either half of the dual basis.
//! \returns The single value in context holding the result of applying
//! `function` to the values held by `first_argument` and `second_argument`.
template <class Impl>
template <class FUNCTION, class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto Applicative<Impl>::zip_with(this auto &&self, FUNCTION &&function,
                                 FIRST_ARGUMENT &&first_argument,
                                 SECOND_ARGUMENT &&second_argument)
    requires requires(const Impl &impl) {
        impl.zip_with(std::forward<FUNCTION>(function),
                      std::forward<FIRST_ARGUMENT>(first_argument),
                      std::forward<SECOND_ARGUMENT>(second_argument));
    } || requires {
        self.invoke(std::forward<FUNCTION>(function),
                    std::forward<FIRST_ARGUMENT>(first_argument),
                    std::forward<SECOND_ARGUMENT>(second_argument));
    }
{
    if constexpr (requires {
                      impl_of(self).zip_with(
                          std::forward<FUNCTION>(function),
                          std::forward<FIRST_ARGUMENT>(first_argument),
                          std::forward<SECOND_ARGUMENT>(second_argument));
                  }) {
        return impl_of(self).zip_with(
            std::forward<FUNCTION>(function),
            std::forward<FIRST_ARGUMENT>(first_argument),
            std::forward<SECOND_ARGUMENT>(second_argument));
    } else {
        return self.invoke(std::forward<FUNCTION>(function),
                           std::forward<FIRST_ARGUMENT>(first_argument),
                           std::forward<SECOND_ARGUMENT>(second_argument));
    }
}

//! \constraints `Impl` provides either a `discard_first` accepting
//! `first_argument` and `second_argument`, or an `invoke` accepting a
//! callable that ignores its first parameter and returns its second,
//! together with `first_argument` and `second_argument` -- an `invoke`
//! native to `Impl` or derived from `Impl`'s basis.
//! \effects If `Impl` provides `discard_first`, the effect is that of
//! `Impl`'s own `discard_first`; otherwise the application is expressed
//! through the object's own `invoke`, applying a callable that discards the
//! value held by `first_argument` and returns the value held by
//! `second_argument`.
//! \returns The single value in context holding the value that
//! `second_argument` holds.
template <class Impl>
template <class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto Applicative<Impl>::discard_first(this auto &&self,
                                      FIRST_ARGUMENT &&first_argument,
                                      SECOND_ARGUMENT &&second_argument)
    requires requires(const Impl &impl) {
        impl.discard_first(std::forward<FIRST_ARGUMENT>(first_argument),
                           std::forward<SECOND_ARGUMENT>(second_argument));
    } || requires {
        self.invoke(discard_first_eval,
                    std::forward<FIRST_ARGUMENT>(first_argument),
                    std::forward<SECOND_ARGUMENT>(second_argument));
    }
{
    if constexpr (requires {
                      impl_of(self).discard_first(
                          std::forward<FIRST_ARGUMENT>(first_argument),
                          std::forward<SECOND_ARGUMENT>(second_argument));
                  }) {
        return impl_of(self).discard_first(
            std::forward<FIRST_ARGUMENT>(first_argument),
            std::forward<SECOND_ARGUMENT>(second_argument));
    } else {
        return self.invoke(discard_first_eval,
                           std::forward<FIRST_ARGUMENT>(first_argument),
                           std::forward<SECOND_ARGUMENT>(second_argument));
    }
}

//! \constraints `Impl` provides either a `discard_second` accepting
//! `first_argument` and `second_argument`, or an `invoke` accepting a
//! callable that returns its first parameter and ignores its second,
//! together with `first_argument` and `second_argument` -- an `invoke`
//! native to `Impl` or derived from `Impl`'s basis.
//! \effects If `Impl` provides `discard_second`, the effect is that of
//! `Impl`'s own `discard_second`; otherwise the application is expressed
//! through the object's own `invoke`, applying a callable that returns the
//! value held by `first_argument` and discards the value held by
//! `second_argument`.
//! \returns The single value in context holding the value that
//! `first_argument` holds.
template <class Impl>
template <class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto Applicative<Impl>::discard_second(this auto &&self,
                                       FIRST_ARGUMENT &&first_argument,
                                       SECOND_ARGUMENT &&second_argument)
    requires requires(const Impl &impl) {
        impl.discard_second(std::forward<FIRST_ARGUMENT>(first_argument),
                            std::forward<SECOND_ARGUMENT>(second_argument));
    } || requires {
        self.invoke(discard_second_eval,
                    std::forward<FIRST_ARGUMENT>(first_argument),
                    std::forward<SECOND_ARGUMENT>(second_argument));
    }
{
    if constexpr (requires {
                      impl_of(self).discard_second(
                          std::forward<FIRST_ARGUMENT>(first_argument),
                          std::forward<SECOND_ARGUMENT>(second_argument));
                  }) {
        return impl_of(self).discard_second(
            std::forward<FIRST_ARGUMENT>(first_argument),
            std::forward<SECOND_ARGUMENT>(second_argument));
    } else {
        return self.invoke(discard_second_eval,
                           std::forward<FIRST_ARGUMENT>(first_argument),
                           std::forward<SECOND_ARGUMENT>(second_argument));
    }
}

// \rSec3[transpose.applicative.grade]{Grade re-indexing}

//! \constraints `value` can be re-indexed to `TARGET_GRADE`.
//! \effects-equiv
//! \remarks An instance that does not participate in grading still provides
//! this member. Such a carrier is graded by the empty set, the only licensed
//! target is the empty set, and the re-indexing is the identity. Grade
//! participation is therefore never something an instance declares.
template <class Impl>
template <class TARGET_GRADE, class CARRIER>
constexpr auto Applicative<Impl>::subsume(this auto &&, CARRIER &&value)
    requires requires {
        grade_subsume<TARGET_GRADE>(std::forward<CARRIER>(value));
    }
{
    return grade_subsume<TARGET_GRADE>(std::forward<CARRIER>(value));
}

// \rSec3[transpose.applicative.delegate]{Delegated application}

//! \effects-equiv
template <class Impl>
template <class APPLICATIVE_MAP, class FUNCTION, class FIRST_ARGUMENT,
          class... REST_ARGUMENTS>
auto Applicative<Impl>::invoke_with(this auto &&,
                                    const APPLICATIVE_MAP &applicative_map,
                                    FUNCTION &&function,
                                    FIRST_ARGUMENT &&first_argument,
                                    REST_ARGUMENTS &&...rest_arguments) {
    return applicative_map.invoke(
        std::forward<FUNCTION>(function),
        std::forward<FIRST_ARGUMENT>(first_argument),
        std::forward<REST_ARGUMENTS>(rest_arguments)...);
}

//! \effects-equiv
template <class Impl>
template <const auto &APPLICATIVE_MAP, class FUNCTION, class FIRST_ARGUMENT,
          class... REST_ARGUMENTS>
auto Applicative<Impl>::invoke_with(this auto &&, FUNCTION &&function,
                                    FIRST_ARGUMENT &&first_argument,
                                    REST_ARGUMENTS &&...rest_arguments) {
    return APPLICATIVE_MAP.invoke(
        std::forward<FUNCTION>(function),
        std::forward<FIRST_ARGUMENT>(first_argument),
        std::forward<REST_ARGUMENTS>(rest_arguments)...);
}

// \rSec3[transpose.applicative.optional]{Applicative instance for optional}

//! \returns An engaged `optional` holding `value`.
template <class VALUE_TYPE>
template <class VALUE>
auto OptionalApplicativeImpl<VALUE_TYPE>::pure(this auto &&, VALUE &&value)
    -> std::optional<remove_cvref_t<VALUE>> {
    return std::optional<remove_cvref_t<VALUE>>{std::forward<VALUE>(value)};
}

//! \returns If every operand is engaged, an engaged `optional` holding the
//! result of invoking `function` with the contained values, in the order
//! written; otherwise a disengaged `optional`.
//! \remarks `function` is invoked at most once.
template <class VALUE_TYPE>
template <class FUNCTION, class FIRST, class... REST>
auto OptionalApplicativeImpl<VALUE_TYPE>::invoke(
    this auto &&, FUNCTION &&function, const std::optional<FIRST> &first,
    const std::optional<REST> &...rest)
    -> std::optional<remove_cvref_t<
        std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>> {
    using Result = remove_cvref_t<
        std::invoke_result_t<FUNCTION &, const FIRST &, const REST &...>>;
    if (first.has_value() && (... && rest.has_value())) {
        return std::optional<Result>{std::invoke(function, *first, *rest...)};
    }
    return std::optional<Result>{};
}

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_APPLY_HPP
