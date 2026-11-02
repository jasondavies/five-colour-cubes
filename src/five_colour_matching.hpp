#pragma once
#include <array>
#include <vector>
#include <bit>
#include <cstdlib>

constexpr int N = 75;
using Owners = std::array<std::array<int, 8>, N>;
std::array<std::array<int, 6>, N> faces;
std::array<std::array<unsigned, N>, N> fits;

struct State {
    std::vector<int> cubes;
    Owners owners;
    std::array<int, N> matched{};
    State() { for (auto &row : owners) row.fill(-1); }

    bool augment(int t, int copy, unsigned &seen) {
        unsigned options = fits[t][cubes[copy]] & ~seen;
        while (options) {
            int k = std::countr_zero(options);
            options &= options - 1;
            if (seen & (1u << k)) continue;
            seen |= 1u << k;
            int old = owners[t][k];
            if (old < 0 || augment(t, old, seen)) {
                owners[t][k] = copy;
                return true;
            }
        }
        return false;
    }

    bool add(int c) {
        auto saved_owners = owners;
        auto saved_matched = matched;
        cubes.push_back(c);
        for (int t = 0; t < N; ++t) {
            unsigned seen = 0;
            if (augment(t, static_cast<int>(cubes.size()) - 1, seen)) {
                if (++matched[t] == 8) {
#ifdef MACMAHON_VERIFY_MATCHES
                    // Check the actual assignment before every search rejection.
                    // This uses only distinct copy indices and the incidence table,
                    // independently of the augmenting-path bookkeeping.
                    for (int k = 0; k < 8; ++k) {
                        int j = owners[t][k];
                        if (j < 0 || j >= static_cast<int>(cubes.size()) ||
                            !(fits[t][cubes[j]] & (1u << k))) std::abort();
                        for (int h = 0; h < k; ++h)
                            if (owners[t][h] == j) std::abort();
                    }
#endif
                    cubes.pop_back();
                    owners = saved_owners;
                    matched = saved_matched;
                    return false;
                }
            }
        }
        return true;
    }
};
