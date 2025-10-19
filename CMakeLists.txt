cmake_minimum_required(VERSION 4.1.2)
project(smtm CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# file(CREATE_LINK
#   "${CMAKE_BINARY_DIR}/compile_commands.json"
#   "${CMAKE_SOURCE_DIR}/compile_commands.json"
#   SYMBOLIC
# )

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(SOURCES src/main.cpp src/anima/deduction.cpp)

add_executable(${PROJECT_NAME} ${SOURCES})

# cvc5

find_package(cvc5)

target_link_libraries(${PROJECT_NAME} PRIVATE cvc5::cvc5 cvc5::cvc5parser)

target_include_directories(
    ${PROJECT_NAME}
    PRIVATE ${PROJECT_SOURCE_DIR}/cvc5/build/include
)
target_include_directories(
    ${PROJECT_NAME}
    PRIVATE ${PROJECT_SOURCE_DIR}/cvc5/include
)

# EnTT

include(FetchContent)
FetchContent_Declare(
    EnTT
    GIT_REPOSITORY https://github.com/skypjack/entt.git
    GIT_TAG v3.15.0
)

FetchContent_MakeAvailable(EnTT)

target_link_libraries(${PROJECT_NAME} PRIVATE EnTT::EnTT)

# SDL3

find_package(SDL3 REQUIRED CONFIG REQUIRED COMPONENTS SDL3-shared)
target_link_libraries(${PROJECT_NAME} PRIVATE SDL3::SDL3)
