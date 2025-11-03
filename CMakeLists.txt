cmake_minimum_required(VERSION 4.1.2)
project(smt-man LANGUAGES C)

set(CMAKE_POLICY_VERSION_MINIMUM 3.5)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)

set(SOURCES src/main.c )

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
    # -DDEBUG
)

include_directories(${PROJECT_SOURCE_DIR}/include)

add_custom_target(
    copy_sprites
    COMMAND
        ${CMAKE_COMMAND} -E copy_directory_if_different
        "${CMAKE_CURRENT_SOURCE_DIR}/resources/"
        "${CMAKE_CURRENT_BINARY_DIR}/resources/"
    COMMENT "Copying data"
)
add_dependencies(${PROJECT_NAME} copy_sprites)

# Libraries

# # External

# # # Threads

set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads)
target_link_libraries(${PROJECT_NAME} PRIVATE Threads::Threads)
message(": ${CMAKE_THREAD_LIBS_INIT}" )


# # # SDL3

find_package(SDL3 REQUIRED CONFIG REQUIRED COMPONENTS SDL3-shared)
target_link_libraries(${PROJECT_NAME} PRIVATE SDL3::SDL3)

# # libpng

find_package(PNG REQUIRED)
target_include_directories(${PROJECT_NAME} PRIVATE ${PNG_INCLUDE_DIR})
target_link_libraries(${PROJECT_NAME} PRIVATE ${PNG_LIBRARY})

# # Submodules

# # # cvc5

find_package(cvc5)

target_link_libraries(${PROJECT_NAME} PRIVATE cvc5::cvc5 cvc5::cvc5parser)

target_include_directories(
    ${PROJECT_NAME}
    PRIVATE
        ${PROJECT_SOURCE_DIR}/cvc5/build/include
        ${PROJECT_SOURCE_DIR}/cvc5/include
)

# # FetchContent

include(FetchContent)

# # cwalk
FetchContent_Declare(
    cwalk
    GIT_REPOSITORY https://github.com/likle/cwalk.git
    GIT_TAG v1.2.9
)

FetchContent_MakeAvailable(cwalk)
target_include_directories(${PROJECT_NAME} PRIVATE ${cwalk_SOURCE_DIR}/include)
target_sources(${PROJECT_NAME} PRIVATE ${cwalk_SOURCE_DIR}/src/cwalk.c)

# # spdlog
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

# # whereami
FetchContent_Declare(
    whereami
    GIT_REPOSITORY https://github.com/gpakosz/whereami.git
)

FetchContent_MakeAvailable(whereami)
target_include_directories(${PROJECT_NAME} PRIVATE ${whereami_SOURCE_DIR}/src)
target_sources(${PROJECT_NAME} PRIVATE ${whereami_SOURCE_DIR}/src/whereami.c)
