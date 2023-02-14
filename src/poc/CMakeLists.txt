cmake_minimum_required(VERSION 3.14)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

set(CMAKE_CXX_STANDARD 17)
set(COMPILER_FLAGS "-Wall --std=c++17 -march=native -funroll-loops")
set(LINKER_FLAGS "-static-libstdc++ -static-libgcc")
set(CMAKE_CXX_FLAGS "${COMPILER_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LINKER_FLAGS}")
#set(CMAKE_CXX_CLANG_TIDY clang-tidy-12 -checks='*')

add_executable(poc_speck speck.cpp)
target_link_libraries(poc_speck)

add_executable(poc_lea lea.cpp)
target_link_libraries(poc_lea)
