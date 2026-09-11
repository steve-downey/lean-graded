# examples/CMakeLists.txt                                           -*-cmake-*-
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

set(ALL_EXAMPLES
    transpose_example
    traverse_example
    apply_example
    fold_example
    soa_aos_example
    binary_tree_example
    algorithm_object_example
    lookup_modes_example
    graded_gadgets_example
    transpose_post_example
    traverse_post_example
)

include(CheckIncludeFileCXX)
check_include_file_cxx(simd BEMAN_TRANSPOSE_HAS_SIMD)
if(BEMAN_TRANSPOSE_HAS_SIMD)
    list(APPEND ALL_EXAMPLES simd_example)
endif()

foreach(example ${ALL_EXAMPLES})
    add_executable(beman.transpose.examples.${example})
    target_sources(beman.transpose.examples.${example} PRIVATE ${example}.cpp)
    target_link_libraries(
        beman.transpose.examples.${example}
        PRIVATE beman::transpose
    )
    add_test(
        NAME beman.transpose.examples.${example}
        COMMAND beman.transpose.examples.${example}
    )
endforeach()
