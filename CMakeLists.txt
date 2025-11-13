cmake_minimum_required(VERSION 4.1.2)
project(smt-man LANGUAGES C)

set(CMAKE_POLICY_VERSION_MINIMUM 3.5)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)

list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake")

set(SOURCES src/main.c)

file(GLOB ANIMA src/anima/*.c)
file(GLOB CORE src/core/*.c)
file(GLOB LOGIC src/logic/*.c)
file(GLOB RENDER src/render/*.c)
file(GLOB UTILS src/utils/*.c)

add_executable(
    ${PROJECT_NAME}
    ${SOURCES}
    ${ANIMA}
    ${CORE}
    ${LOGIC}
    ${RENDER}
    ${UTILS}
)

target_compile_options(
    ${PROJECT_NAME}
    PRIVATE
        # -Wall
        -Werror
        -g
        -O0
        -DDEBUG
)

include_directories(${PROJECT_SOURCE_DIR}/include)

# Libraries

find_package(PkgConfig REQUIRED)

set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads)
target_link_libraries(${PROJECT_NAME} PRIVATE Threads::Threads)

# pkg_check_modules(SDL3 REQUIRED SDL3)
find_package(SDL3 REQUIRED CONFIG REQUIRED COMPONENTS SDL3-shared)
target_link_libraries(${PROJECT_NAME} PRIVATE SDL3::SDL3 SDL3::Headers)
target_include_directories(${PROJECT_NAME} PRIVATE ${SDL3_INCLUDE_DIRS})

# pkg_check_modules(LIBPNG REQUIRED LIBPNG)
find_package(PNG REQUIRED)
target_link_libraries(${PROJECT_NAME} PRIVATE PNG::PNG)
target_include_directories(${PROJECT_NAME} PRIVATE ${PNG_INCLUDE_DIRS})

find_package(Criterion REQUIRED)
target_link_libraries(${PROJECT_NAME} PRIVATE criterion)

## Submodules

### cvc5

find_package(cvc5)
target_link_libraries(${PROJECT_NAME} PRIVATE cvc5::cvc5 cvc5::cvc5parser)
target_include_directories(
    ${PROJECT_NAME}
    PRIVATE
        ${PROJECT_SOURCE_DIR}/deps/cvc5/build/include
        ${PROJECT_SOURCE_DIR}/deps/cvc5/include
)

## FetchContent

include(FetchContent)

FetchContent_Declare(
    cwalk
    GIT_REPOSITORY https://github.com/likle/cwalk.git
    GIT_TAG v1.2.9
)
# FetchContent_MakeAvailable(cwalk)
target_include_directories(${PROJECT_NAME} PRIVATE ${cwalk_SOURCE_DIR}/include)
target_sources(${PROJECT_NAME} PRIVATE ${cwalk_SOURCE_DIR}/src/cwalk.c)

FetchContent_Declare(
    stumpless
    GIT_REPOSITORY git@github.com:goatshriek/stumpless.git
    GIT_TAG v2.2.0
)
FetchContent_MakeAvailable(stumpless)
target_link_libraries(${PROJECT_NAME} PRIVATE stumpless)
target_include_directories(
    ${PROJECT_NAME}
    PRIVATE ${stumpless_SOURCE_DIR}/include ${stumpless_BINARY_DIR}/include
)

FetchContent_Declare(
    whereami
    GIT_REPOSITORY https://github.com/gpakosz/whereami.git
)
FetchContent_MakeAvailable(whereami)
target_include_directories(${PROJECT_NAME} PRIVATE ${whereami_SOURCE_DIR}/src)
target_sources(${PROJECT_NAME} PRIVATE ${whereami_SOURCE_DIR}/src/whereami.c)

add_custom_target(
    copy_data
    COMMAND
        ${CMAKE_COMMAND} -E copy_directory_if_different
        "${CMAKE_CURRENT_SOURCE_DIR}/resources/"
        "${CMAKE_CURRENT_BINARY_DIR}/resources/"
    COMMENT "Copying data"
)
add_dependencies(${PROJECT_NAME} copy_data)

add_subdirectory("tests")
