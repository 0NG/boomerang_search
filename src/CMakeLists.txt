cmake_minimum_required(VERSION 3.14)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

set(CMAKE_CXX_STANDARD 17)
set(COMPILER_FLAGS "-Wall --std=c++17 -march=native -funroll-loops")
set(LINKER_FLAGS "-static-libstdc++ -static-libgcc")
set(CMAKE_CXX_FLAGS "${COMPILER_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LINKER_FLAGS}")
#set(CMAKE_CXX_CLANG_TIDY clang-tidy-12 -checks='*')

add_subdirectory(poc)
add_subdirectory(3rd)
include_directories(${CMAKE_CURRENT_LIST_DIR}/3rd/or-tools)

# ==== speck ====
add_executable(speck_boomerang2 speck_boomerang2.cpp)
target_link_libraries(speck_boomerang2 ortools::ortools)

add_executable(speck_boomerang_enum speck_boomerang_enum.cpp)
target_link_libraries(speck_boomerang_enum ortools::ortools)

# ==== lea ====
add_executable(lea_boomerang_enum lea_boomerang_enum.cpp)
target_link_libraries(lea_boomerang_enum ortools::ortools)
