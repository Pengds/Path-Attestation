cmake_minimum_required(VERSION 3.12)
project(OptimizedControlFlowPass)

set(CMAKE_CXX_STANDARD 17)

find_package(LLVM REQUIRED CONFIG)

include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_subdirectory(ControlFlowIRPass)