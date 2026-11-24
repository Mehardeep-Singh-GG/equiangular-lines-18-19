#pragma once
#include <algorithm>
#include <array>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

// Small-buffer vector of uint32_t limbs (inline up to 16 limbs = 512 bits, zero heap allocs in hot paths)
struct SmallLimbs {
    static constexpr size_t INLINE_CAP = 16;
    size_t sz = 0;
    bool using_heap = false;
    std::array<uint32_t, INLINE_CAP> inl{};
    std::vector<uint32_t> heap;

    SmallLimbs() = default;
    SmallLimbs(const SmallLimbs& o) : sz(o.sz), using_heap(o.using_heap) {
        if (using_heap) heap = o.heap;
        else for (size_t i = 0; i < sz; ++i) inl[i] = o.inl[i];
    }
    SmallLimbs(SmallLimbs&& o) noexcept : sz(o.sz), using_heap(o.using_heap) {
        if (using_heap) heap = std::move(o.heap);
        else for (size_t i = 0; i < sz; ++i) inl[i] = o.inl[i];
        o.sz = 0; o.using_heap = false;
    }
    SmallLimbs& operator=(const SmallLimbs& o) {
        if (this == &o) return *this;
        sz = o.sz; using_heap = o.using_heap;
        if (using_heap) heap = o.heap;
        else { heap.clear(); for (size_t i = 0; i < sz; ++i) inl[i] = o.inl[i]; }
        return *this;
    }
    SmallLimbs& operator=(SmallLimbs&& o) noexcept {
        if (this == &o) return *this;
        sz = o.sz; using_heap = o.using_heap;
        if (using_heap) heap = std::move(o.heap);
        else { heap.clear(); for (size_t i = 0; i < sz; ++i) inl[i] = o.inl[i]; }
        o.sz = 0; o.using_heap = false;
        return *this;
    }

    size_t size() const { return sz; }
    bool empty() const { return sz == 0; }
    uint32_t operator[](size_t i) const { return using_heap ? heap[i] : inl[i]; }
    uint32_t& operator[](size_t i) { return using_heap ? heap[i] : inl[i]; }
    uint32_t back() const { return (*this)[sz - 1]; }
    void pop_back() {
        --sz;
        if (using_heap) heap.pop_back();
    }
    void push_back(uint32_t v) {
        if (!using_heap) {
            if (sz < INLINE_CAP) { inl[sz++] = v; return; }
            heap.assign(inl.begin(), inl.begin() + sz);
            using_heap = true;
        }
        heap.push_back(v);
        ++sz;
    }
    void resize(size_t n, uint32_t v = 0) {
        if (n <= INLINE_CAP && !using_heap) {
            for (size_t i = sz; i < n; ++i) inl[i] = v;
            sz = n;
            return;
        }
        if (!using_heap) {
            heap.assign(inl.begin(), inl.begin() + sz);
            using_heap = true;
        }
        heap.resize(n, v);
        sz = n;
    }
    void assign(size_t n, uint32_t v) {
        if (n <= INLINE_CAP) {
            using_heap = false;
            heap.clear();
            sz = n;
            for (size_t i = 0; i < n; ++i) inl[i] = v;
        } else {
            using_heap = true;
            heap.assign(n, v);
            sz = n;
        }
    }
};

struct BigInt {
    int sign = 0; // 0 for zero, +1 or -1
    SmallLimbs limbs; // little-endian base 2^32

    BigInt() = default;
    BigInt(int64_t v) {
        if (v == 0) { sign = 0; }
        else if (v > 0) {
            sign = 1;
            uint64_t u = static_cast<uint64_t>(v);
            while (u) { limbs.push_back(static_cast<uint32_t>(u & 0xFFFFFFFFu)); u >>= 32; }
        } else {
            sign = -1;
            uint64_t u = static_cast<uint64_t>(-(v + 1)) + 1ULL;
            while (u) { limbs.push_back(static_cast<uint32_t>(u & 0xFFFFFFFFu)); u >>= 32; }
        }
    }

    static BigInt from_u64(uint64_t u) {
        BigInt r;
        if (u == 0) return r;
        r.sign = 1;
        while (u) { r.limbs.push_back(static_cast<uint32_t>(u & 0xFFFFFFFFu)); u >>= 32; }
        return r;
    }

    void trim() {
        while (!limbs.empty() && limbs.back() == 0) limbs.pop_back();
        if (limbs.empty()) sign = 0;
    }

    bool is_zero() const { return sign == 0; }
    bool is_even() const { return limbs.empty() || (limbs[0] & 1u) == 0; }

    BigInt operator-() const {
        BigInt r = *this;
        r.sign = -r.sign;
        return r;
    }

    BigInt abs() const {
        BigInt r = *this;
        if (r.sign < 0) r.sign = 1;
        return r;
    }

    static int cmp_abs(const BigInt& a, const BigInt& b) {
        if (a.limbs.size() != b.limbs.size())
            return a.limbs.size() < b.limbs.size() ? -1 : 1;
        for (size_t i = a.limbs.size(); i-- > 0;) {
            if (a.limbs[i] != b.limbs[i])
                return a.limbs[i] < b.limbs[i] ? -1 : 1;
        }
        return 0;
    }

    static int cmp(const BigInt& a, const BigInt& b) {
        if (a.sign != b.sign) return a.sign < b.sign ? -1 : 1;
        if (a.sign == 0) return 0;
        return a.sign * cmp_abs(a, b);
    }

    bool operator==(const BigInt& o) const { return cmp(*this, o) == 0; }
    bool operator!=(const BigInt& o) const { return cmp(*this, o) != 0; }
    bool operator<(const BigInt& o) const { return cmp(*this, o) < 0; }
    bool operator<=(const BigInt& o) const { return cmp(*this, o) <= 0; }
    bool operator>(const BigInt& o) const { return cmp(*this, o) > 0; }
    bool operator>=(const BigInt& o) const { return cmp(*this, o) >= 0; }

    static BigInt add_abs(const BigInt& a, const BigInt& b) {
        BigInt r;
        size_t n = std::max(a.limbs.size(), b.limbs.size());
        r.limbs.resize(n, 0);
        uint64_t carry = 0;
        for (size_t i = 0; i < n; ++i) {
            uint64_t sum = carry;
            if (i < a.limbs.size()) sum += a.limbs[i];
            if (i < b.limbs.size()) sum += b.limbs[i];
            r.limbs[i] = static_cast<uint32_t>(sum & 0xFFFFFFFFu);
            carry = sum >> 32;
        }
        if (carry) r.limbs.push_back(static_cast<uint32_t>(carry));
        r.sign = r.limbs.empty() ? 0 : 1;
        r.trim();
        return r;
    }

    static BigInt sub_abs(const BigInt& a, const BigInt& b) {
        BigInt r;
        r.limbs.resize(a.limbs.size(), 0);
        int64_t borrow = 0;
        for (size_t i = 0; i < a.limbs.size(); ++i) {
            int64_t diff = static_cast<int64_t>(a.limbs[i]) - borrow;
            if (i < b.limbs.size()) diff -= static_cast<int64_t>(b.limbs[i]);
            if (diff < 0) {
                diff += (1LL << 32);
                borrow = 1;
            } else {
                borrow = 0;
            }
            r.limbs[i] = static_cast<uint32_t>(diff);
        }
        r.sign = 1;
        r.trim();
        return r;
    }

    BigInt operator+(const BigInt& o) const {
        if (sign == 0) return o;
        if (o.sign == 0) return *this;
        if (sign == o.sign) {
            BigInt r = add_abs(*this, o);
            r.sign = sign;
            return r;
        }
        int c = cmp_abs(*this, o);
        if (c == 0) return BigInt(0);
        if (c > 0) {
            BigInt r = sub_abs(*this, o);
            r.sign = sign;
            return r;
        } else {
            BigInt r = sub_abs(o, *this);
            r.sign = o.sign;
            return r;
        }
    }

    BigInt operator-(const BigInt& o) const { return *this + (-o); }

    BigInt operator*(const BigInt& o) const {
        if (sign == 0 || o.sign == 0) return BigInt(0);
        BigInt r;
        r.limbs.assign(limbs.size() + o.limbs.size(), 0);
        for (size_t i = 0; i < limbs.size(); ++i) {
            uint64_t carry = 0;
            uint64_t ai = limbs[i];
            for (size_t j = 0; j < o.limbs.size(); ++j) {
                uint64_t cur = r.limbs[i + j] + ai * o.limbs[j] + carry;
                r.limbs[i + j] = static_cast<uint32_t>(cur & 0xFFFFFFFFu);
                carry = cur >> 32;
            }
            r.limbs[i + o.limbs.size()] += static_cast<uint32_t>(carry);
        }
        r.sign = sign * o.sign;
        r.trim();
        return r;
    }

    BigInt operator<<(uint32_t k) const {
        if (sign == 0 || k == 0) return *this;
        uint32_t word_shift = k / 32;
        uint32_t bit_shift = k % 32;
        BigInt r;
        r.sign = sign;
        r.limbs.assign(word_shift, 0);
        uint32_t carry = 0;
        for (size_t i = 0; i < limbs.size(); ++i) {
            uint32_t w = limbs[i];
            r.limbs.push_back((w << bit_shift) | carry);
            carry = bit_shift ? (w >> (32 - bit_shift)) : 0;
        }
        if (carry) r.limbs.push_back(carry);
        r.trim();
        return r;
    }

    BigInt operator>>(uint32_t k) const {
        if (sign == 0 || k == 0) return *this;
        uint32_t word_shift = k / 32;
        uint32_t bit_shift = k % 32;
        if (word_shift >= limbs.size()) return BigInt(0);
        BigInt r;
        r.sign = sign;
        r.limbs.resize(limbs.size() - word_shift);
        for (size_t i = word_shift; i < limbs.size(); ++i) {
            uint32_t lo = limbs[i] >> bit_shift;
            uint32_t hi = (bit_shift && i + 1 < limbs.size()) ? (limbs[i + 1] << (32 - bit_shift)) : 0;
            r.limbs[i - word_shift] = lo | hi;
        }
        r.trim();
        return r;
    }

    size_t bit_length() const {
        if (sign == 0) return 0;
        uint32_t top = limbs.back();
        size_t bits = (limbs.size() - 1) * 32;
        while (top) { ++bits; top >>= 1; }
        return bits;
    }

    static void divmod(const BigInt& a, const BigInt& b, BigInt& q, BigInt& r) {
        if (b.is_zero()) throw std::runtime_error("division by zero");
        if (a.is_zero()) { q = BigInt(0); r = BigInt(0); return; }
        int c = cmp_abs(a, b);
        if (c < 0) { q = BigInt(0); r = a; return; }
        if (c == 0) { q = BigInt(a.sign * b.sign); r = BigInt(0); return; }

        BigInt abs_b = b.abs();
        if (abs_b.limbs.size() == 1) {
            uint64_t d = abs_b.limbs[0];
            q.limbs.assign(a.limbs.size(), 0);
            uint64_t rem = 0;
            for (size_t i = a.limbs.size(); i-- > 0;) {
                uint64_t cur = (rem << 32) | a.limbs[i];
                q.limbs[i] = static_cast<uint32_t>(cur / d);
                rem = cur % d;
            }
            q.sign = a.sign * b.sign;
            q.trim();
            r = BigInt::from_u64(rem);
            if (!r.is_zero()) r.sign = a.sign;
            return;
        }

        size_t ba = a.bit_length();
        size_t bb = abs_b.bit_length();
        size_t shift = ba - bb;
        BigInt rem = a.abs();
        BigInt cur = abs_b << static_cast<uint32_t>(shift);
        q.limbs.assign((shift / 32) + 1, 0);
        for (size_t s = shift + 1; s-- > 0;) {
            if (cmp_abs(rem, cur) >= 0) {
                rem = sub_abs(rem, cur);
                q.limbs[s / 32] |= (1u << (s % 32));
            }
            if (s > 0) cur = cur >> 1;
        }
        q.sign = a.sign * b.sign;
        q.trim();
        r = rem;
        if (!r.is_zero()) r.sign = a.sign;
    }

    BigInt operator/(const BigInt& o) const {
        BigInt q, r;
        divmod(*this, o, q, r);
        return q;
    }

    BigInt operator%(const BigInt& o) const {
        BigInt q, r;
        divmod(*this, o, q, r);
        return r;
    }

    static BigInt gcd(BigInt a, BigInt b) {
        a = a.abs();
        b = b.abs();
        if (a.is_zero()) return b;
        if (b.is_zero()) return a;
        uint32_t shift = 0;
        auto ctz = [](const BigInt& x) -> uint32_t {
            uint32_t z = 0;
            for (size_t i = 0; i < x.limbs.size(); ++i) {
                uint32_t w = x.limbs[i];
                if (w == 0) z += 32;
                else { z += static_cast<uint32_t>(__builtin_ctz(w)); break; }
            }
            return z;
        };
        uint32_t za = ctz(a);
        uint32_t zb = ctz(b);
        shift = std::min(za, zb);
        a = a >> za;
        b = b >> zb;
        while (!b.is_zero()) {
            b = b >> ctz(b);
            if (cmp_abs(a, b) > 0) std::swap(a, b);
            b = sub_abs(b, a);
        }
        return a << shift;
    }

    std::string to_string() const {
        if (sign == 0) return "0";
        BigInt tmp = abs();
        std::string s;
        BigInt base(1000000000);
        while (!tmp.is_zero()) {
            BigInt q, r;
            divmod(tmp, base, q, r);
            uint32_t rem = r.limbs.empty() ? 0 : r.limbs[0];
            std::string chunk = std::to_string(rem);
            if (!q.is_zero()) chunk = std::string(9 - chunk.size(), '0') + chunk;
            std::reverse(chunk.begin(), chunk.end());
            s += chunk;
            tmp = std::move(q);
        }
        if (sign < 0) s.push_back('-');
        std::reverse(s.begin(), s.end());
        return s;
    }
};
