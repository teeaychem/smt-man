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

# include(FetchContent)
# FetchContent_Declare(
#   EnTT
#   GIT_REPOSITORY https://github.com/skypjack/entt.git
#   GIT_TAG        v3.15.0
# )

# FetchContent_MakeAvailable(EnTT)
message(${PROJECT_SOURCE_DIR}/cvc5/include)

# include_directories(${PROJECT_SOURCE_DIR}/cvc5)
find_package(cvc5)


add_executable(smtm src/main.cpp)

target_include_directories(smtm PRIVATE ${PROJECT_SOURCE_DIR}/cvc5/build/include)
target_include_directories(smtm PRIVATE ${PROJECT_SOURCE_DIR}/cvc5/include)

# target_link_libraries(smtm PRIVATE EnTT::EnTT)
target_link_libraries(smtm PRIVATE cvc5::cvc5 cvc5::cvc5parser)
