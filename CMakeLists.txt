cmake_minimum_required(VERSION 4.1.2)

project(smt-man-build)

set(SUBMODULES ${CMAKE_CURRENT_SOURCE_DIR}/submodules)
add_library(
    slog
    STATIC
    ${SUBMODULES}/slog/src/slog.c
    ${SUBMODULES}/slog/src/slog.h
)
target_compile_options(slog PRIVATE ${COMPILE_FLAGS})

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/lib)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/bin)
