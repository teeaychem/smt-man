cmake_minimum_required(VERSION 4.1.2)

project(smt-man LANGUAGES C)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)

set(COMPILE_FLAGS
    -Wall
    -Wextra
    -Wpedantic
    -Wformat-security
    -Wnull-dereference
    -Wwrite-strings
    -Wformat=2
    -Wconversion
    -Wunreachable-code
    -g3
    -O3
    # -DDEBUG
)

set(COMPILE_AND_LINK_OPTIONS
    -fsanitize=undefined
    -fsanitize=address
    -fno-omit-frame-pointer
)

list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake")

# libraries
set(SMTMANLIB ${PROJECT_NAME}-lib)

set(SUBMODULES ${CMAKE_CURRENT_SOURCE_DIR}/../submodules)

find_package(PkgConfig REQUIRED)

find_package(Threads)
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)

pkg_check_modules(SDL3 REQUIRED SDL3)
find_package(SDL3 REQUIRED CONFIG REQUIRED COMPONENTS SDL3-shared)

pkg_check_modules(LIBPNG REQUIRED LIBPNG)
find_package(PNG REQUIRED)

# targets

include_directories(${PROJECT_SOURCE_DIR}/include)

file(GLOB MAIN src/main.c src/setup.c)
file(GLOB_RECURSE RENDER src/render/*.c)
file(GLOB_RECURSE SPRITES src/sprite/*.c)

# # main

add_executable(${PROJECT_NAME} ${MAIN} ${RENDER} ${SPRITES})
target_compile_options(
    ${PROJECT_NAME}
    PRIVATE # ${COMPILE_FLAGS}
)
# add_link_options(${PROJECT_NAME} ${COMPILE_AND_LINK_OPTIONS})

target_include_directories(
    ${PROJECT_NAME}
    PRIVATE ${PROJECT_SOURCE_DIR}/include
)

# # #

target_link_libraries(${PROJECT_NAME} PRIVATE Threads::Threads)

target_link_libraries(${PROJECT_NAME} PRIVATE SDL3::SDL3 SDL3::Headers)

target_link_libraries(${PROJECT_NAME} PRIVATE PNG::PNG)
target_include_directories(${PROJECT_NAME} PRIVATE ${PNG_INCLUDE_DIRS})

# # #

target_include_directories(
    ${PROJECT_NAME}
    PRIVATE ${PROJECT_SOURCE_DIR}/../lib/include
)

target_link_libraries(${PROJECT_NAME} PRIVATE ${SMTMANLIB})

# # #

target_include_directories(${PROJECT_NAME} PRIVATE ${SUBMODULES}/cwalk/include)
target_sources(${PROJECT_NAME} PRIVATE ${SUBMODULES}/cwalk/src/cwalk.c)

target_include_directories(${PROJECT_NAME} PRIVATE ${SUBMODULES}/whereami/src)
target_sources(${PROJECT_NAME} PRIVATE ${SUBMODULES}/whereami/src/whereami.c)

# # resources

add_custom_target(
    copy_data
    COMMAND
        ${CMAKE_COMMAND} -E copy_directory_if_different
        "${CMAKE_CURRENT_SOURCE_DIR}/resources/"
        "${CMAKE_CURRENT_BINARY_DIR}/resources/"
    COMMENT "Copying data"
)
add_dependencies(${PROJECT_NAME} copy_data)

# # # scratch

add_executable(z3_scratch src/z3_scratch.c src/setup.c ${SPRITES})
target_compile_options(z3_scratch PRIVATE ${COMPILE_FLAGS})

# # #

target_include_directories(
    z3_scratch
    PRIVATE ${PROJECT_SOURCE_DIR}/../lib/include
)

target_link_libraries(z3_scratch PRIVATE z3)

# # #

target_link_libraries(z3_scratch PRIVATE ${SMTMANLIB})
target_include_directories(z3_scratch PRIVATE ${PROJECT_SOURCE_DIR}/include)

# # #

target_include_directories(z3_scratch PRIVATE ${SUBMODULES}/cwalk/include)
target_sources(z3_scratch PRIVATE ${SUBMODULES}/cwalk/src/cwalk.c)

target_sources(z3_scratch PRIVATE ${SUBMODULES}/whereami/src/whereami.c)
target_include_directories(z3_scratch PRIVATE ${SUBMODULES}/whereami/src)

# Tests

# add_subdirectory("tests")
