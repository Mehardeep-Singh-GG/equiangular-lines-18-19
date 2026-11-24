#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

// Compute top 8 coefficients of charpoly(M) mod 128:
// det(I - t*M) mod (t^8, 128) = sum_{j=0}^7 c[j] t^j, where charpoly(x) = sum c[j] x^(n-j).
static std::array<uint8_t, 8> charpoly_top8_mod128(int n, const std::vector<uint8_t>& M) {
    // M is n x n row-major mod 128
    std::array<uint8_t, 8> p{};
    p[0] = 1;
    // Process from bottom-right upward: at step s (k = n - 1 - s down to 0),
    // submatrix is rows/cols k..n-1 of size sz = n - k.
    // Wait: simpler to go k = 0 .. n-1 adding row/col k to submatrix 0..k-1!
    for (int k = 0; k < n; ++k) {
        uint8_t a = M[k * n + k];
        std::array<uint8_t, 8> v{};
        v[0] = 1;
        v[1] = static_cast<uint8_t>((128 - a) & 127);
        if (k > 0) {
            // C is column M[0..k-1, k], R is row M[k, 0..k-1]
            std::vector<uint8_t> vec(k);
            for (int i = 0; i < k; ++i) vec[i] = M[i * n + k];
            for (int j = 2; j < 8; ++j) {
                uint32_t dot = 0;
                for (int i = 0; i < k; ++i) {
                    dot += static_cast<uint32_t>(M[k * n + i]) * vec[i];
                }
                v[j] = static_cast<uint8_t>((128 - (dot & 127)) & 127);
                if (j + 1 < 8) {
                    std::vector<uint8_t> next_vec(k, 0);
                    for (int r = 0; r < k; ++r) {
                        uint32_t s = 0;
                        for (int c = 0; c < k; ++c) {
                            s += static_cast<uint32_t>(M[r * n + c]) * vec[c];
                        }
                        next_vec[r] = static_cast<uint8_t>(s & 127);
                    }
                    vec = std::move(next_vec);
                }
            }
        }
        std::array<uint8_t, 8> np{};
        for (int i = 0; i < 8; ++i) {
            uint32_t s = 0;
            for (int j = 0; j <= i; ++j) {
                s += static_cast<uint32_t>(v[j]) * p[i - j];
            }
            np[i] = static_cast<uint8_t>(s & 127);
        }
        p = np;
    }
    return p;
}

int main(int argc, char** argv) {
    int n = (argc >= 2) ? std::stoi(argv[1]) : 49;
    int samples = (argc >= 3) ? std::stoi(argv[2]) : 40000;
    std::string raw_json = (argc >= 4) ? argv[3] : "";
    int d = (argc >= 5) ? std::stoi(argv[4]) : 17;
    int c_shift = (argc >= 6) ? std::stoi(argv[5]) : 9;

    std::mt19937_64 rng(42);
    std::set<std::array<uint8_t, 8>> P_set;
    std::vector<uint8_t> M(n * n);

    for (int it = 0; it < samples; ++it) {
        // S + I has 1 on diag, +/-1 off-diag (mod 128: 1 or 127)
        // Note: switching D(S+I)D preserves charpoly, so fix row/col 0 to all 1s!
        for (int i = 0; i < n; ++i) M[i * n + i] = 1;
        for (int j = 1; j < n; ++j) M[j] = M[j * n] = 1;
        for (int i = 1; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                uint8_t val = (rng() & 1) ? 1 : 127;
                M[i * n + j] = M[j * n + i] = val;
            }
        }
        auto sig = charpoly_top8_mod128(n, M);
        P_set.insert(sig);
        if ((it + 1) % 5000 == 0) {
            std::cout << "  after " << (it + 1) << " samples: |P_{" << n << ",7}| = " << P_set.size() << "\n";
        }
        if (P_set.size() == 2048) {
            std::cout << "  HIT 2048 at sample " << (it + 1) << "!\n";
            break;
        }
    }
    std::cout << "Final |P_{" << n << ",7}| = " << P_set.size() << "\n";

    if (!raw_json.empty()) {
        std::ifstream ifs(raw_json);
        std::string content((std::istreambuf_iterator<char>(ifs)), std::istreambuf_iterator<char>());
        // Quick parse of "polys": [ [...] ]
        auto pos = content.find("\"polys\":");
        if (pos == std::string::npos) return 1;
        int matched = 0, total = 0;
        size_t cur = pos;
        while (true) {
            auto lb = content.find('[', cur);
            if (lb == std::string::npos) break;
            if (lb == content.find('[', pos)) { cur = lb + 1; continue; } // outer [
            auto rb = content.find(']', lb);
            if (rb == std::string::npos) break;
            std::string row = content.substr(lb + 1, rb - lb - 1);
            cur = rb + 1;
            std::vector<int64_t> b;
            std::stringstream ss(row);
            std::string tok;
            while (std::getline(ss, tok, ',')) {
                b.push_back(std::stoll(tok));
            }
            if (static_cast<int>(b.size()) != d + 1) continue;
            ++total;

            // Convert Q(w) to charpoly of S + I:
            // f(x) = 2^(d-1) * Q((x - c_shift)/2)
            // Note: S + I has eigenvalue lambda + 1. Let z = lambda + 1, so lambda = z - 1.
            // charpoly_{S+I}(z) = (z + 4)^(n - d) * f(z - 1)
            // Here f(z - 1) = 2^(d-1) * Q((z - 1 - c_shift)/2).
            // Since c_shift is odd, c_shift + 1 is even: let 2*s = c_shift + 1!
            // Then (z - 1 - c_shift)/2 = (z - 2*s)/2 = z/2 - s.
            // Wait: 2^(d-1) * Q(z/2 - s) = sum_{j=0}^d b[j] * 2^(j - 1) * (z - 2*s)^(d - j)
            // WAIT: for j=0, b[0]=2, so 2^(-1) * 2 = 1!
            // That means f(z - 1) = sum_{j=0}^d (b[j] * 2^(j-1) if j>=1 else 1) * (z - 2*s)^(d - j)!!
            // Let's compute top 8 coeffs (in descending powers of z, i.e., c[0]*z^n + c[1]*z^(n-1) + ... + c[7]*z^(n-7)) mod 128!
            // Using t = 1/z:
            // t^n * charpoly_{S+I}(1/t) = (1 + 4t)^(n-d) * sum_{j=0}^d coeff_j * t^j * (1 - 2*s*t)^(d - j) mod t^8!
            int s = (c_shift + 1) / 2;
            auto mul_poly8 = [](const std::array<uint8_t, 8>& A, const std::array<uint8_t, 8>& B) {
                std::array<uint8_t, 8> R{};
                for (int i = 0; i < 8; ++i) {
                    uint32_t acc = 0;
                    for (int j = 0; j <= i; ++j) acc += static_cast<uint32_t>(A[j]) * B[i - j];
                    R[i] = static_cast<uint8_t>(acc & 127);
                }
                return R;
            };
            auto pow_linear8 = [&](int64_t alpha, int e) {
                // (1 + alpha * t)^e mod (t^8, 128)
                std::array<uint8_t, 8> res{}, base{};
                res[0] = 1;
                base[0] = 1;
                base[1] = static_cast<uint8_t>((alpha % 128 + 128) % 128);
                while (e > 0) {
                    if (e & 1) res = mul_poly8(res, base);
                    base = mul_poly8(base, base);
                    e >>= 1;
                }
                return res;
            };

            std::array<uint8_t, 8> f_rev{};
            for (int j = 0; j < 8 && j <= d; ++j) {
                int64_t cj = (j == 0) ? 1 : ((b[j] % 128 + 128) % 128) * ((1LL << (j - 1)) % 128);
                cj %= 128;
                auto term = pow_linear8(-2 * s, d - j);
                for (int k = 0; k + j < 8; ++k) {
                    f_rev[j + k] = static_cast<uint8_t>((f_rev[j + k] + cj * term[k]) & 127);
                }
            }
            auto factor4 = pow_linear8(4, n - d);
            auto full_sig = mul_poly8(factor4, f_rev);
            if (P_set.count(full_sig)) ++matched;
        }
        std::cout << "Filtered " << total << " raw polys against P_{" << n << ",7}: " << matched << " survive!\n";
    }
    return 0;
}
