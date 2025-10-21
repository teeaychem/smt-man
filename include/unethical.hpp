#pragma once

#include "utils.hpp"
#include <cstdint>
constexpr int32_t kTileSize{16};
constexpr int kGridScale{10};

constexpr Size dMaze{14, 15};
constexpr Size dPixels{dMaze.scale(kTileSize)};
constexpr Size dScreen{dPixels.scale(kGridScale)};

constexpr int kScreenFps{30};
