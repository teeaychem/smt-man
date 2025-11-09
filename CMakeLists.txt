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
        -DDEBUG
)

include_directories(${PROJECT_SOURCE_DIR}/include)

add_custom_target(
    copy_data
    COMMAND
        ${CMAKE_COMMAND} -E copy_directory_if_different
        "${CMAKE_CURRENT_SOURCE_DIR}/resources/"
        "${CMAKE_CURRENT_BINARY_DIR}/resources/"
    COMMENT "Copying data"
)
add_dependencies(${PROJECT_NAME} copy_data)

include(CMakeLibraries.txt)
