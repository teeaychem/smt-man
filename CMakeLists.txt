cmake_minimum_required(VERSION 4.1.2)

project(smt-man LANGUAGES C)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)

list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake")

file(GLOB MAIN src/main.c src/setup.c src/z3.c)
file(GLOB_RECURSE SPRITES src/sprites/*.c)
file(GLOB CORE src/core/*.c)
file(GLOB LOGIC src/logic/*.c)
file(GLOB RENDER src/render/*.c)
file(GLOB UTILS src/utils/*.c)

add_executable(
    ${PROJECT_NAME}
    ${MAIN}
    ${SPRITES}
    ${CORE}
    ${LOGIC}
    ${RENDER}
    ${UTILS}
)

set(COMPILE_AND_LINK_OPTIONS
    -fsanitize={address,undefined}
    -fno-omit-frame-pointer
)
add_compile_options(${COMPILE_AND_LINK_OPTIONS})
add_link_options(${COMPILE_AND_LINK_OPTIONS})

target_compile_options(
    ${PROJECT_NAME}
    PRIVATE
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

include_directories(${PROJECT_SOURCE_DIR}/include)

# Libraries

find_package(PkgConfig REQUIRED)

find_package(Threads)
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
target_link_libraries(${PROJECT_NAME} PRIVATE Threads::Threads)

pkg_check_modules(SDL3 REQUIRED SDL3)
find_package(SDL3 REQUIRED CONFIG REQUIRED COMPONENTS SDL3-shared)
target_link_libraries(${PROJECT_NAME} PRIVATE SDL3::SDL3 SDL3::Headers)

pkg_check_modules(LIBPNG REQUIRED LIBPNG)
find_package(PNG REQUIRED)
target_link_libraries(${PROJECT_NAME} PRIVATE PNG::PNG)
target_include_directories(${PROJECT_NAME} PRIVATE ${PNG_INCLUDE_DIRS})

# find_package(Criterion REQUIRED)
# target_link_libraries(${PROJECT_NAME} PRIVATE criterion)

find_package(z3 REQUIRED CONFIG)
target_link_libraries(${PROJECT_NAME} PRIVATE z3)

pkg_check_modules(GLIB2 glib-2.0)
find_package(PkgConfig REQUIRED)
pkg_search_module(GLIB REQUIRED glib-2.0)
target_include_directories(${PROJECT_NAME} PRIVATE ${GLIB_INCLUDE_DIRS})
target_link_libraries(${PROJECT_NAME} PRIVATE ${GLIB_LIBRARIES})

## Submodules
set(SUBMODULES ${CMAKE_CURRENT_SOURCE_DIR}/submodules)

target_include_directories(${PROJECT_NAME} PRIVATE ${SUBMODULES}/cwalk/include)
target_sources(${PROJECT_NAME} PRIVATE ${SUBMODULES}/cwalk/src/cwalk.c)

target_include_directories(${PROJECT_NAME} PRIVATE ${SUBMODULES}/whereami/src)
target_sources(${PROJECT_NAME} PRIVATE ${SUBMODULES}/whereami/src/whereami.c)

# Resources

add_custom_target(
    copy_data
    COMMAND
        ${CMAKE_COMMAND} -E copy_directory_if_different
        "${CMAKE_CURRENT_SOURCE_DIR}/resources/"
        "${CMAKE_CURRENT_BINARY_DIR}/resources/"
    COMMENT "Copying data"
)
add_dependencies(${PROJECT_NAME} copy_data)

# Tests

# add_subdirectory("tests")
