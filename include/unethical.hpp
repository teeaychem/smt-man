#pragma once

#include "utils.hpp"
#include <cstdint>
constexpr uint32_t kTileSize{16};
constexpr int32_t kSpritePixelCount{kTileSize * kTileSize};

constexpr int kGridScale{2};

constexpr Size dMaze{28, 31};
constexpr Size dPixels{dMaze.scale(kTileSize)};
constexpr Size dScreen{dPixels.scale(kGridScale)};

constexpr int kScreenFps{30};

typedef uint8_t PixelInfo;
typedef uint8_t SpritePixels[kSpritePixelCount];

constexpr Uint64 nsPerFrame = 1000000000 / kScreenFps;
