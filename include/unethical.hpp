#pragma once

constexpr int kTileSize{16};

constexpr int kGridHeight{15};
constexpr int kGridWidth{14};

constexpr int kGridHeightPixels{kGridHeight * kTileSize};
constexpr int kGridWidthPixels{kGridWidth * kTileSize};

constexpr int kGridScale{6};

constexpr int kScreenWidth{kGridWidthPixels * kGridScale};
constexpr int kScreenHeight{kGridHeightPixels * kGridScale};
constexpr int kScreenFps{30};

constexpr int tileSize{16};
