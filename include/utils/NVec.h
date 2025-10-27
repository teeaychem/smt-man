#pragma once

#include <sys/syslog.h>
#include <vector>

#include "stumpless/log.h"


typedef uint32_t nvec_t;

struct NVec {
  std::vector<nvec_t> elements;

  ~NVec() {};

  NVec() { this->elements = std::vector<nvec_t>{}; };

  NVec(nvec_t a, nvec_t b) { this->elements = std::vector<nvec_t>{a, b}; }

  NVec(const NVec &other) { this->elements = other.elements; }

  NVec(NVec &&other) : elements(std::move(other.elements)) {}

  nvec_t elem(size_t index) const {
    if (index < this->elements.size()) {
      return this->elements[index];
    } else {
      stumplog(LOG_CRIT, "NVec overrun %d/%d", index, this->elements.size());
      exit(-1);
    }
  }

  nvec_t x() const { return this->elem(0); }
  nvec_t y() const { return this->elem(1); }

  nvec_t area() const {
    nvec_t area{1};
    for (auto &elem : this->elements) {
      area *= elem;
    }
    return area;
  }

  void multiply(nvec_t value) {
    for (size_t idx{0}; idx < this->elements.size(); ++idx) {
      this->elements[idx] *= value;
    }
  }
};


typedef NVec Size;
