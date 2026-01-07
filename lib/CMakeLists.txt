cmake_minimum_required(VERSION 4.1.2)

project(smt-man-lib LANGUAGES C)

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

file(GLOB_RECURSE SPRITES src/sprites/*.c)
file(GLOB CORE src/core/*.c)
file(GLOB LOGIC src/logic/*.c)
file(GLOB UTILS src/utils/*.c)

# libraries
set(SUBMODULES ${CMAKE_CURRENT_SOURCE_DIR}/../submodules)

find_package(PkgConfig REQUIRED)

find_package(Threads)
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)

pkg_check_modules(SDL3 REQUIRED SDL3)
find_package(SDL3 REQUIRED CONFIG REQUIRED COMPONENTS SDL3-shared)

# find_package(Criterion REQUIRED)
# target_link_libraries(${PROJECT_NAME} PRIVATE criterion)

find_package(z3 REQUIRED CONFIG)

# target

add_library(${PROJECT_NAME} STATIC ${SPRITES} ${CORE} ${LOGIC} ${UTILS})
target_compile_options(
    ${PROJECT_NAME}
    PRIVATE
        ${COMPILE_FLAGS} #${COMPILE_AND_LINK_OPTIONS}
)

# # includes

target_include_directories(${PROJECT_NAME} PUBLIC ${PROJECT_SOURCE_DIR}/include)

# # libs

target_link_libraries(${PROJECT_NAME} PRIVATE Threads::Threads)
target_link_libraries(${PROJECT_NAME} PRIVATE z3)

target_link_libraries(${PROJECT_NAME} INTERFACE slog)
target_include_directories(${PROJECT_NAME} PUBLIC ${SUBMODULES}/slog/src/)
