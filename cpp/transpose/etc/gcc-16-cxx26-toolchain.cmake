# etc/gcc-16-cxx26-toolchain.cmake                                  -*-cmake-*-
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
# gcc-16 at C++26: the gcc-16 toolchain with the standard raised so that
# <simd> (P1928) is available. Used by the papers/blog examples build.

include_guard(GLOBAL)

include("${CMAKE_CURRENT_LIST_DIR}/gcc-16-toolchain.cmake")

set(CMAKE_CXX_STANDARD 26)
string(REPLACE "gnu++23" "gnu++26" _bt_cxx26_flags "${CMAKE_CXX_FLAGS}")
set(CMAKE_CXX_FLAGS "${_bt_cxx26_flags}" CACHE STRING "CXX_FLAGS" FORCE)
