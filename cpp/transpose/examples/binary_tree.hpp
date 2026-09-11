// examples/binary_tree.hpp                                           -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Shared example header: BinaryTree<T> data type with Foldable, Applicative,
// and Traversable typeclass instances. Not part of the proposed library.
#ifndef EXAMPLE_BINARY_TREE_HPP
#define EXAMPLE_BINARY_TREE_HPP

#include <beman/transpose/apply.hpp>
#include <beman/transpose/fold.hpp>
#include <beman/transpose/monoid.hpp>
#include <beman/transpose/traverse.hpp>

#include <cassert>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

namespace example {

/** Persistent binary tree where every node carries a value.
 * Nodes are either leaves (no children) or internal nodes with left and right
 * subtrees. Sharing is structural: subtrees are held by shared_ptr, so copies
 * are cheap and the tree is immutable once built.
 * @tparam T element type stored at every node
 */
template <class T>
class BinaryTree {
    T d_value;
    std::shared_ptr<BinaryTree> d_left;
    std::shared_ptr<BinaryTree> d_right;

  public:
    using value_type = T;

    /** Construct a leaf node holding @p value (no children). */
    static auto leaf(T value) -> BinaryTree {
        return BinaryTree(std::move(value), {}, {});
    }

    /** Construct an internal node with @p value and two children. */
    static auto node(T value, BinaryTree left, BinaryTree right) -> BinaryTree {
        return BinaryTree(std::move(value),
                          std::make_shared<BinaryTree>(std::move(left)),
                          std::make_shared<BinaryTree>(std::move(right)));
    }

    /** Alias for node(); prefer node() in new code. */
    static auto branch(T value, BinaryTree left, BinaryTree right)
        -> BinaryTree {
        return node(std::move(value), std::move(left), std::move(right));
    }

    /** Low-level constructor accepting pre-built child shared_ptrs.
     * Null pointers represent absent children.
     */
    static auto from_children_ptrs(T value, std::shared_ptr<BinaryTree> left,
                                   std::shared_ptr<BinaryTree> right)
        -> BinaryTree {
        return BinaryTree(std::move(value), std::move(left), std::move(right));
    }

    /** Heap-allocate a copy of @p tree and return the owning pointer. */
    static auto make_ptr(BinaryTree tree) -> std::shared_ptr<BinaryTree> {
        return std::make_shared<BinaryTree>(std::move(tree));
    }

    /** Return the value stored at this node. */
    auto value() const -> const T & { return d_value; }

    /** True when this node has a left child. */
    auto has_left() const -> bool { return static_cast<bool>(d_left); }
    /** True when this node has a right child. */
    auto has_right() const -> bool { return static_cast<bool>(d_right); }

    /** Return the left child; precondition: has_left(). */
    auto left() const -> const BinaryTree & {
        assert(d_left);
        return *d_left;
    }

    /** Return the right child; precondition: has_right(). */
    auto right() const -> const BinaryTree & {
        assert(d_right);
        return *d_right;
    }

    /** Shared pointer to the left child; may be null. */
    auto left_ptr() const -> const std::shared_ptr<BinaryTree> & {
        return d_left;
    }
    /** Shared pointer to the right child; may be null. */
    auto right_ptr() const -> const std::shared_ptr<BinaryTree> & {
        return d_right;
    }

  private:
    BinaryTree(T value, std::shared_ptr<BinaryTree> left,
               std::shared_ptr<BinaryTree> right)
        : d_value(std::move(value)), d_left(std::move(left)),
          d_right(std::move(right)) {}
};

// ---------------------------------------------------------------------------
// Foldable instance for BinaryTree<T>
// ---------------------------------------------------------------------------

/** Foldable typeclass instance for BinaryTree<T>.
 * fold_map applies @p function to every node value (in-order: left, root,
 * right) and combines the results using the Monoid for the return type.
 * @tparam T element type of the tree being folded
 */
template <class T>
struct BinaryTreeFoldableImpl {
    template <class F>
    auto fold_map(this auto &&self, F &&function, const BinaryTree<T> &tree)
        -> beman::transpose::remove_cvref_t<
            decltype(std::invoke(function, tree.value()))> {
        auto value_result = std::invoke(function, tree.value());
        using Result = beman::transpose::remove_cvref_t<decltype(value_result)>;

        Result acc = tree.has_left() ? beman::transpose::monoid_combine(
                                           self.fold_map(function, tree.left()),
                                           std::move(value_result))
                                     : std::move(value_result);

        if (tree.has_right()) {
            acc = beman::transpose::monoid_combine(
                std::move(acc), self.fold_map(function, tree.right()));
        }

        return acc;
    }
};

/** Foldable map that exposes the fold_map operation for BinaryTree<T>. */
template <class T>
struct BinaryTreeFoldableMap
    : beman::transpose::Foldable<BinaryTreeFoldableImpl<T>> {
    using BinaryTreeFoldableImpl<T>::fold_map;
};

// ---------------------------------------------------------------------------
// Applicative instance for BinaryTree<T>
// ---------------------------------------------------------------------------

/** Applicative typeclass instance for BinaryTree<T> with shape-aware
 * semantics.
 *
 * pure(v) produces a single leaf. ap recurses pairwise over matching tree
 * structure: a leaf function distributes over the argument's shape; a leaf
 * argument distributes over the function's shape; when both have children,
 * only positions where both trees have a child are combined (pairwise).
 * These are monad-derived (not zip) applicative semantics.
 *
 * DELIBERATELY ap-basis: this instance is the living exemplar that ap is
 * a perfectly cromulent basis for Applicative. The base derives the
 * user-facing n-ary `invoke` from pure + ap via terminating partial
 * application, while invoke-native instances (optional, sender, std::simd)
 * go the other way. The shape-aware pairwise recursion is a case where
 * one-step application is the genuinely natural formulation: each
 * recursion step really does hold functions in the context.
 * @tparam T element type of the function tree (F is the function type stored)
 */
template <class T>
struct BinaryTreeApplicativeImpl {
    /** Lift a plain value into a single-leaf tree. */
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value) {
        using U = beman::transpose::remove_cvref_t<VALUE>;
        return BinaryTree<U>::leaf(std::forward<VALUE>(value));
    }

    /**
     * @brief One-step application of a tree of functions to a tree of
     * arguments, shape-aware.
     * @param functions tree whose nodes contain callables
     * @param arguments tree whose nodes contain arguments
     * @return tree of results; shape determined by pairwise recursion rules
     */
    template <class F, class A>
    auto ap(this auto &&self, const BinaryTree<F> &functions,
            const BinaryTree<A> &arguments)
        -> BinaryTree<std::invoke_result_t<const F &, const A &>> {
        using R = std::invoke_result_t<const F &, const A &>;

        std::shared_ptr<BinaryTree<R>> left{};
        std::shared_ptr<BinaryTree<R>> right{};

        const auto function_is_leaf =
            !functions.has_left() && !functions.has_right();
        const auto argument_is_leaf =
            !arguments.has_left() && !arguments.has_right();

        if (function_is_leaf) {
            // pure(f) should distribute f over the argument shape.
            if (arguments.has_left()) {
                left = BinaryTree<R>::make_ptr(
                    self.ap(functions, arguments.left()));
            }
            if (arguments.has_right()) {
                right = BinaryTree<R>::make_ptr(
                    self.ap(functions, arguments.right()));
            }
        } else if (argument_is_leaf) {
            // A non-leaf function tree can be applied pointwise to a single
            // argument.
            if (functions.has_left()) {
                left = BinaryTree<R>::make_ptr(
                    self.ap(functions.left(), arguments));
            }
            if (functions.has_right()) {
                right = BinaryTree<R>::make_ptr(
                    self.ap(functions.right(), arguments));
            }
        } else {
            // If both have shape, recurse pairwise where both children exist.
            if (functions.has_left() && arguments.has_left()) {
                left = BinaryTree<R>::make_ptr(
                    self.ap(functions.left(), arguments.left()));
            }

            if (functions.has_right() && arguments.has_right()) {
                right = BinaryTree<R>::make_ptr(
                    self.ap(functions.right(), arguments.right()));
            }
        }

        return BinaryTree<R>::from_children_ptrs(
            functions.value()(arguments.value()), std::move(left),
            std::move(right));
    }
};

/** Applicative map for BinaryTree<T>: ap-basis; the base derives the
 * user-facing n-ary invoke. */
template <class T>
struct BinaryTreeApplicativeMap
    : beman::transpose::Applicative<BinaryTreeApplicativeImpl<T>> {
    using BinaryTreeApplicativeImpl<T>::ap;
    using BinaryTreeApplicativeImpl<T>::pure;
};

// ---------------------------------------------------------------------------
// Traversable instance for BinaryTree<T>
// ---------------------------------------------------------------------------

/** Traversable typeclass instance for BinaryTree<T>.
 * traverse maps each node value into an applicative context and rebuilds a
 * BinaryTree inside that context, preserving the original tree's shape.
 * @tparam T element type of the tree being traversed
 */
template <class T>
struct BinaryTreeTraversableImpl {
    using element_type = T;

    template <class APPLICATIVE, class F>
    auto traverse(this auto &&self, const APPLICATIVE &applicative,
                  F &&function, const BinaryTree<T> &tree) {
        auto value_context =
            std::invoke(std::forward<F>(function), tree.value());
        using Context =
            beman::transpose::remove_cvref_t<decltype(value_context)>;
        using U = beman::transpose::applicative_value_t<Context>;
        using TreeContext = decltype(applicative.invoke(
            [](auto &&value) {
                using V = beman::transpose::remove_cvref_t<decltype(value)>;
                return BinaryTree<V>::leaf(
                    std::forward<decltype(value)>(value));
            },
            value_context));

        if (!tree.has_left() && !tree.has_right()) {
            return applicative.invoke(
                [](auto &&value) {
                    using V = beman::transpose::remove_cvref_t<decltype(value)>;
                    return BinaryTree<V>::leaf(
                        std::forward<decltype(value)>(value));
                },
                value_context);
        }

        std::optional<TreeContext> left_tree_context;
        if (tree.has_left()) {
            left_tree_context.emplace(
                self.traverse(applicative, function, tree.left()));
        }

        std::optional<TreeContext> right_tree_context;
        if (tree.has_right()) {
            right_tree_context.emplace(
                self.traverse(applicative, function, tree.right()));
        }

        auto to_child_ptr = [&](const auto &child_tree_context) {
            return applicative.invoke(
                [](auto &&subtree) {
                    using SubTree =
                        beman::transpose::remove_cvref_t<decltype(subtree)>;
                    return std::make_shared<SubTree>(
                        std::forward<decltype(subtree)>(subtree));
                },
                child_tree_context);
        };

        auto empty_child_like = [&](const auto &child_tree_context) {
            return applicative.invoke(
                [](const auto &) { return std::shared_ptr<BinaryTree<U>>{}; },
                child_tree_context);
        };

        auto left_context = [&]() {
            if (left_tree_context.has_value()) {
                return to_child_ptr(*left_tree_context);
            }

            return empty_child_like(*right_tree_context);
        }();

        auto right_context = [&]() {
            if (right_tree_context.has_value()) {
                return to_child_ptr(*right_tree_context);
            }

            return empty_child_like(*left_tree_context);
        }();

        return applicative.invoke(
            [](auto &&value, auto &&left, auto &&right) {
                using V = beman::transpose::remove_cvref_t<decltype(value)>;
                return BinaryTree<V>::from_children_ptrs(
                    std::forward<decltype(value)>(value),
                    std::forward<decltype(left)>(left),
                    std::forward<decltype(right)>(right));
            },
            value_context, left_context, right_context);
    }
};

/** Traversable map that exposes traverse for BinaryTree<T>. */
template <class T>
struct BinaryTreeTraversableMap
    : beman::transpose::Traversable<BinaryTreeTraversableImpl<T>> {
    using BinaryTreeTraversableImpl<T>::traverse;
};

} // namespace example

namespace beman::transpose {

// ---------------------------------------------------------------------------
// Typeclass registrations for example::BinaryTree<T>
// ---------------------------------------------------------------------------

/** Registers BinaryTreeFoldableMap as the Foldable instance for
 * example::BinaryTree<T>. */
template <class T>
inline constexpr auto foldable_typeclass<example::BinaryTree<T>> =
    example::BinaryTreeFoldableMap<T>{};

/** Registers BinaryTreeApplicativeMap as the Applicative instance for
 * example::BinaryTree<T>. */
template <class T>
inline constexpr auto applicative_typeclass<example::BinaryTree<T>> =
    example::BinaryTreeApplicativeMap<T>{};

/** Registers BinaryTreeTraversableMap as the Traversable instance for
 * example::BinaryTree<T>. */
template <class T>
inline constexpr auto traversable_typeclass<example::BinaryTree<T>> =
    example::BinaryTreeTraversableMap<T>{};

} // namespace beman::transpose

#endif // EXAMPLE_BINARY_TREE_HPP
