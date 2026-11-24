#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

static std::array<uint8_t, 8> charpoly_top8_mod128(int n, const std::vector<uint8_t>& M) {
    std::array<uint8_t, 8> p{};
    p[0] = 1;
    for (int k = 0; k < n; ++k) {
        uint8_t a = M[k * n + k];
        std::array<uint8_t, 8> v{};
        v[0] = 1;
        v[1] = static_cast<uint8_t>((128 - a) & 127);
        if (k > 0) {
            std::vector<uint8_t> vec(k);
            for (int i = 0; i < k; ++i) vec[i] = M[i * n + k];
            for (int j = 2; j < 8; ++j) {
                uint32_t dot = 0;
                for (int i = 0; i < k; ++i) dot += static_cast<uint32_t>(M[k * n + i]) * vec[i];
                v[j] = static_cast<uint8_t>((128 - (dot & 127)) & 127);
                if (j + 1 < 8) {
                    std::vector<uint8_t> next_vec(k, 0);
                    for (int r = 0; r < k; ++r) {
                        uint32_t s = 0;
                        for (int c = 0; c < k; ++c) s += static_cast<uint32_t>(M[r * n + c]) * vec[c];
                        next_vec[r] = static_cast<uint8_t>(s & 127);
                    }
                    vec = std::move(next_vec);
                }
            }
        }
        std::array<uint8_t, 8> np{};
        for (int i = 0; i < 8; ++i) {
            uint32_t s = 0;
            for (int j = 0; j <= i; ++j) s += static_cast<uint32_t>(v[j]) * p[i - j];
            np[i] = static_cast<uint8_t>(s & 127);
        }
        p = np;
    }
    return p;
}

int main(int argc, char** argv) {
    if (argc < 5) {
        std::cerr << "Usage: " << argv[0] << " <d> <n> <c_shift> <raw_json> [out_json]\n";
        return 1;
    }
    int d = std::stoi(argv[1]);
    int n = std::stoi(argv[2]);
    int c_shift = std::stoi(argv[3]);
    std::string raw_json = argv[4];
    std::string out_json = (argc >= 6) ? argv[5] : "";
    bool n_even = (n % 2 == 0);
    size_t target_size = n_even ? 1024 : 2048;

    std::mt19937_64 rng(1234567ULL + n);
    std::set<std::array<uint8_t, 8>> P_set;
    std::vector<uint8_t> M(n * n);
    for (int it = 0; it < 100000; ++it) {
        for (int i = 0; i < n; ++i) M[i * n + i] = 1;
        for (int j = 1; j < n; ++j) M[j] = M[j * n] = 1;
        for (int i = 1; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                uint8_t val = (rng() & 1) ? 1 : 127;
                M[i * n + j] = M[j * n + i] = val;
            }
        }
        P_set.insert(charpoly_top8_mod128(n, M));
        if (P_set.size() == target_size) break;
    }
    std::cout << "|P_{" << n << ",7}| = " << P_set.size() << " (expected " << target_size << ")\n";

    std::ifstream ifs(raw_json);
    std::string content((std::istreambuf_iterator<char>(ifs)), std::istreambuf_iterator<char>());
    auto pos = content.find("\"polys\":");
    if (pos == std::string::npos) return 1;

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

    std::vector<std::vector<int64_t>> kept;
    int total = 0;
    size_t cur = pos;
    while (true) {
        auto lb = content.find('[', cur);
        if (lb == std::string::npos) break;
        if (lb == content.find('[', pos)) { cur = lb + 1; continue; }
        auto rb = content.find(']', lb);
        if (rb == std::string::npos) break;
        std::string row = content.substr(lb + 1, rb - lb - 1);
        cur = rb + 1;
        std::vector<int64_t> b;
        std::stringstream ss(row);
        std::string tok;
        while (std::getline(ss, tok, ',')) b.push_back(std::stoll(tok));
        if (static_cast<int>(b.size()) != d + 1) continue;
        ++total;

        std::array<uint8_t, 8> f_rev{};
        for (int j = 0; j < 8 && j <= d; ++j) {
            int64_t cj = 0;
            if (n_even) {
                // b[0] = 1, f(z-1) = sum b[j] * 2^j * (z - 2s)^(d-j)
                cj = ((b[j] % 128 + 128) % 128) * ((1LL << j) % 128);
            } else {
                // b[0] = 2, f(z-1) = sum (j==0 ? 1 : b[j]*2^(j-1)) * (z - 2s)^(d-j)
                cj = (j == 0) ? 1 : ((b[j] % 128 + 128) % 128) * ((1LL << (j - 1)) % 128);
            }
            cj %= 128;
            auto term = pow_linear8(-2 * s, d - j);
            for (int k = 0; k + j < 8; ++k) {
                f_rev[j + k] = static_cast<uint8_t>((f_rev[j + k] + cj * term[k]) & 127);
            }
        }
        auto full_sig = mul_poly8(pow_linear8(4, n - d), f_rev);
        if (P_set.count(full_sig)) kept.push_back(std::move(b));
    }

    std::cout << "Filtered (" << d << "," << n << "): " << total << " -> " << kept.size() << " survive P_{" << n << ",7}\n";
    if (!out_json.empty()) {
        std::ofstream ofs(out_json);
        ofs << "{\n  \"d\": " << d << ", \"n\": " << n << ", \"c\": " << c_shift
            << ", \"raw_count\": " << total << ", \"count\": " << kept.size() << ",\n  \"polys\": [\n";
        for (size_t i = 0; i < kept.size(); ++i) {
            ofs << "    [";
            for (size_t j = 0; j < kept[i].size(); ++j)
                ofs << kept[i][j] << (j + 1 < kept[i].size() ? ", " : "");
            ofs << "]" << (i + 1 < kept.size() ? "," : "") << "\n";
        }
        ofs << "  ]\n}\n";
    }
    return 0;
}
