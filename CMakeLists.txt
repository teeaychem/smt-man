cmake_minimum_required(VERSION 4.1.2)
project(smtm LANGUAGES C CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# file(CREATE_LINK
#   "${CMAKE_BINARY_DIR}/compile_commands.json"
#   "${CMAKE_SOURCE_DIR}/compile_commands.json"
#   SYMBOLIC
# )

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)


set(CMAKE_C_STANDARD 17)

set(SOURCES
    src/main.cpp
    src/anima/anima.cpp
    src/anima/deduction.cpp
    src/utils/utils.cpp
    src/visual/textures.cpp
)

add_executable(${PROJECT_NAME} ${SOURCES})

include_directories(${PROJECT_SOURCE_DIR}/include)
message("Source: ${PROJECT_SOURCE_DIR}")
message("Buidling to: ${CMAKE_CURRENT_BINARY_DIR}")
message("Sprites in: ${CMAKE_CURRENT_SOURCE_DIR}/resources/")

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

# # EnTT
FetchContent_Declare(
    EnTT
    GIT_REPOSITORY https://github.com/skypjack/entt.git
    GIT_TAG v3.15.0
)

FetchContent_MakeAvailable(EnTT)
target_link_libraries(${PROJECT_NAME} PRIVATE EnTT::EnTT)

# # whereami
FetchContent_Declare(
    whereami
    GIT_REPOSITORY https://github.com/gpakosz/whereami.git
)

FetchContent_MakeAvailable(whereami)
message(${whereami_SOURCE_DIR})
target_include_directories(${PROJECT_NAME} PRIVATE ${whereami_SOURCE_DIR}/src)
target_sources(${PROJECT_NAME} PRIVATE ${whereami_SOURCE_DIR}/src/whereami.c)
