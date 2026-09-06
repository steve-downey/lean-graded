// include/beman/transpose/grade.hpp                                  -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_GRADE_HPP
#define BEMAN_TRANSPOSE_GRADE_HPP

/// The grade algebra: framework vocabulary only.
///
/// A grade is a compile-time index on an effectful computation. This header
/// says what a grade algebra IS and how the framework asks questions of one.
/// It says nothing whatever about errors. `error_set`, `recover`, and
/// ⊆-as-may-raise are the vocabulary of one particular MODEL, and they live in
/// the model's header; an abstraction whose framework layer names its only
/// model is renamed, not generic. See docs/decisions.md#grade-generality and
/// docs/decisions.md#grade-machinery-home.
///
/// Nothing here is on the typeclass surface. `grade_of` and `rebind_grade` are
/// framework traits; `grade_of` defaults unregistered carriers to the
/// ungraded sentinel, while models own registered carrier specializations.
/// The algebra verbs are free functions in the shape the library already uses
/// for `monoid_combine` and `monoid_identity` -- see
/// docs/decisions.md#grade-operation-spelling for why they carry the `grade_`
/// prefix rather than taking the bare name `join`, which is already the
/// monadic join.
///
/// The load-bearing default is `grade_of`: an instance that knows nothing
/// about grades is treated as uniformly ∅-graded and keeps working verbatim.
/// That default IS the backward-compatibility mechanism of
/// docs/decisions.md#grading-footprint, not a convenience.

#include <beman/transpose/detail/typeclass_base.hpp>

#include <concepts>
#include <type_traits>
#include <utility>

namespace beman::transpose {

//! \remarks `unit_grade` is the sentinel for an ungraded computation. It is
//! deliberately not a grade in any model's lattice: a framework default that
//! were some model's bottom would name that model in order to say "in no
//! grade family at all". Where an ungraded operand meets a graded one, the
//! model lifts the ungraded operand to its own bottom.
struct unit_grade {};

// -- Algebra verbs. Primaries are undefined on purpose: a type is a grade
// -- exactly when a model has registered these for it, so an unregistered
// -- type fails the concept instead of silently behaving like one.

//! \remarks `grade_join<LEFT, RIGHT>::type` is the least upper bound of
//! `LEFT` and `RIGHT`. The primary template is not defined: a type is a
//! grade exactly when a model has registered these operations for it, so an
//! unregistered type fails `grade_semilattice` rather than behaving as a
//! grade.
template <class LEFT, class RIGHT>
struct grade_join;

//! \remarks `grade_bottom<GRADE>::type` is the identity of join in
//! `GRADE`'s algebra. The primary template is not defined.
template <class GRADE>
struct grade_bottom;

//! \remarks `grade_subsumes<LEFT, RIGHT>::value` is `true` when `LEFT`
//! subsumes into `RIGHT`. The order is read off the join: it holds exactly
//! when `grade_join_t<LEFT, RIGHT>` is `RIGHT`. Reading the order off the
//! join is what makes the inclusion between two grades unique, and therefore
//! makes a subsumption coercion canonical. The primary template is not
//! defined.
template <class LEFT, class RIGHT>
struct grade_subsumes;

//! \remarks `grade_model<GRADE>::type` names the model `GRADE` belongs to.
//! A model specializes this for its own grades. The primary template is not
//! defined.
template <class GRADE>
struct grade_model;

template <class LEFT, class RIGHT>
using grade_join_t = typename grade_join<LEFT, RIGHT>::type;

template <class GRADE>
using grade_bottom_t = typename grade_bottom<GRADE>::type;

template <class LEFT, class RIGHT>
inline constexpr bool grade_subsumes_v = grade_subsumes<LEFT, RIGHT>::value;

//! \remarks `grade_semilattice<GRADE>` is satisfied when a model has given
//! `GRADE` a model identity and the three algebra operations. The concept is
//! syntactic. That join is commutative, idempotent and associative, and that
//! bottom is its unit, are semantic requirements on a model, not part of the
//! concept: making them part of it would evaluate a law check in every
//! constraint that mentions a grade.
template <class GRADE>
concept grade_semilattice = requires {
    typename grade_model<GRADE>::type;
    typename grade_join<GRADE, GRADE>::type;
    typename grade_bottom<GRADE>::type;
    { grade_subsumes<GRADE, GRADE>::value } -> std::convertible_to<bool>;
};

// -- Carrier traits -------------------------------------------------------

//! \remarks `grade_of<CONTEXT>::type` is the grade `CONTEXT` carries. The
//! primary template answers `unit_grade`, so a context that knows nothing
//! about grading is treated as ungraded and behaves exactly as it did before
//! grading existed. A model specializes this for the carriers it grades.
template <class CONTEXT>
struct grade_of {
    using type = unit_grade;
};

template <class CONTEXT>
using grade_of_t = typename grade_of<CONTEXT>::type;

//! \remarks `rebind_grade<CONTEXT, GRADE>::type` is `CONTEXT` re-indexed at
//! `GRADE`. The primary template is not defined: only a model knows how its
//! grade is spelled into a carrier, and `unit_grade` is not a grade and has
//! no carrier of its own.
template <class CONTEXT, class GRADE>
struct rebind_grade;

template <class CONTEXT, class GRADE>
using rebind_grade_t = typename rebind_grade<CONTEXT, GRADE>::type;

//! \remarks `graded_context<CONTEXT>` is satisfied when `CONTEXT` carries a
//! model grade rather than `unit_grade`. Graded and ungraded paths are kept
//! mutually exclusive by this constraint rather than by overload ranking.
template <class CONTEXT>
concept graded_context = !std::is_same_v<grade_of_t<CONTEXT>, unit_grade>;

// -- Model identity and detail helpers ------------------------------------

template <class GRADE>
using grade_model_t = typename grade_model<GRADE>::type;

namespace detail {

template <class... GRADES>
struct grade_join_all;

//! \omit
template <class GRADE>
struct grade_join_all<GRADE> {
    using type = GRADE;
};

//! \omit
template <class LEFT, class RIGHT, class... REST>
struct grade_join_all<LEFT, RIGHT, REST...>
    : grade_join_all<grade_join_t<LEFT, RIGHT>, REST...> {};

template <class... GRADES>
using grade_join_all_t = typename grade_join_all<GRADES...>::type;

//! \omit
template <class MODEL_GRADE, class OPERAND>
struct grade_lifted_into_model {
  private:
    using raw_grade = grade_of_t<remove_cvref_t<OPERAND>>;

  public:
    using type = std::conditional_t<std::is_same_v<raw_grade, unit_grade>,
                                    grade_bottom_t<MODEL_GRADE>, raw_grade>;
};

template <class MODEL_GRADE, class OPERAND>
using grade_lifted_into_model_t =
    typename grade_lifted_into_model<MODEL_GRADE, OPERAND>::type;

//! \expos
template <class MODEL_GRADE, class RAW_GRADE>
struct mixes_with_model_impl
    : std::bool_constant<std::is_same_v<grade_model_t<RAW_GRADE>,
                                        grade_model_t<MODEL_GRADE>>> {};

template <class MODEL_GRADE>
struct mixes_with_model_impl<MODEL_GRADE, unit_grade> : std::true_type {};

//! \expos
template <class MODEL_GRADE, class OPERAND>
concept mixes_with_model =
    mixes_with_model_impl<MODEL_GRADE,
                          grade_of_t<remove_cvref_t<OPERAND>>>::value;

template <class MODEL_GRADE, class... OPERANDS>
    requires(sizeof...(OPERANDS) > 0) &&
                (mixes_with_model<MODEL_GRADE, OPERANDS> && ...)
using mixed_grade_t =
    grade_join_all_t<grade_lifted_into_model_t<MODEL_GRADE, OPERANDS>...>;

//! \expos
//! \seebelow
template <class MODEL_GRADE, class CARRIER, class... OPERANDS>
using mixed_result_t =
    rebind_grade_t<CARRIER, mixed_grade_t<MODEL_GRADE, OPERANDS...>>;

/** Value-level evidence combination at one grade.
 *
 * Implementation detail for the accumulating expected object. The default is
 * left-biased same-type evidence, enough for single-slot errors; models with
 * multi-witness evidence can add a detail overload in their own header.
 */
template <class EVIDENCE>
constexpr auto combine_grade_evidence(const EVIDENCE &lhs,
                                      const EVIDENCE & /*rhs*/) -> EVIDENCE {
    return lhs;
}

} // namespace detail

// \rSec3[transpose.grade.subsume]{Subsumption}

//! \constraints `TARGET_GRADE` satisfies `grade_semilattice`; the grade
//! `value` carries is either `unit_grade` or subsumes into `TARGET_GRADE`;
//! and `value`'s carrier re-indexed at `TARGET_GRADE` is constructible from
//! `value`.
//! \effects-equiv
//! \returns `value`'s carrier re-indexed at `TARGET_GRADE`, holding the same
//! computation.
//! \remarks The coercion is the carrier's own converting constructor. No
//! separate machinery is needed: because the order is read off the join, the
//! inclusion between two grades is unique, so there is exactly one coercion
//! and the carrier already provides it. The source grade may be
//! `unit_grade`; the target must be a model grade.
template <class TARGET_GRADE, class CARRIER>
    requires grade_semilattice<TARGET_GRADE> &&
             (std::is_same_v<grade_of_t<remove_cvref_t<CARRIER>>, unit_grade> ||
              grade_subsumes_v<grade_of_t<remove_cvref_t<CARRIER>>,
                               TARGET_GRADE>) &&
             std::constructible_from<
                 rebind_grade_t<remove_cvref_t<CARRIER>, TARGET_GRADE>, CARRIER>
constexpr auto grade_subsume(CARRIER &&value)
    -> rebind_grade_t<remove_cvref_t<CARRIER>, TARGET_GRADE> {
    return rebind_grade_t<remove_cvref_t<CARRIER>, TARGET_GRADE>(
        std::forward<CARRIER>(value));
}

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_GRADE_HPP
