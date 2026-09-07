# include/beman/transpose/CMakeLists.txt                            -*-cmake-*-
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

target_sources(
    beman.transpose
    INTERFACE
        FILE_SET HEADERS
            FILES
                config.hpp
                apply.hpp
                array.hpp
                dual_monoid.hpp
                error_set.hpp
                expected.hpp
                fold.hpp
                functor.hpp
                grade.hpp
                monad.hpp
                monoid.hpp
                sender.hpp
                sequence.hpp
                transpose.hpp
                traverse.hpp
                zip_list.hpp
                simd.hpp
                simd_lanes.hpp
                detail/applicative_derivation.hpp
                detail/typeclass_base.hpp
                "${PROJECT_BINARY_DIR}/include/beman/transpose/config_generated.hpp"
)
