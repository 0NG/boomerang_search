#pragma once

#include "absl/numeric/int128.h"

#include <array>
#include <vector>
#include <cstdint>

#include <iostream>
using std::cout;
using std::endl;

static inline bool carry(const bool a, const bool b, const bool c)
{
    return (a & b) ^ (a & c) ^ (b & c);
}

static inline bool borrow(const bool a, const bool b, const bool c)
{
    const bool na = a ^ 1;
    return (na & b) | (na & c) | (a & b & c);
}

static inline unsigned char bct_transfer(const unsigned char state, const bool l, const bool r, const bool dL, const bool dR, const bool nL, const bool nR)
{
    const bool c1 = (state >> 0) & 1;
    const bool b1 = (state >> 1) & 1;
    const bool c2 = (state >> 2) & 1;
    const bool b2 = (state >> 3) & 1;
    const bool tmp1 = carry(l, r, c1);
    const bool tmp2 = borrow(l ^ r ^ c1 ^ nL, r ^ nR, b1);
    const bool tmp3 = carry(l ^ dL, r ^ dR, c2);
    const bool tmp4 = borrow(l ^ dL ^ r ^ dR ^ c2 ^ nL, r ^ dR ^ nR, b2);
    return (tmp4 << 3) ^ (tmp3 << 2) ^ (tmp2 << 1) ^ (tmp1 << 0);
}

unsigned long long int bct_entry(unsigned int dL, unsigned int dR, unsigned int nL, unsigned int nR, const int nbit = 16)
{
    const std::vector<std::vector<int>> table = {{
        {{ 4, 2, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0 }},
        {{ 2, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2 }},
        {{ 2, 2, 0, 0, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0 }},
        {{ 2, 0, 0, 0, 2, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2 }},
        {{ 2, 0, 2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2 }},
        {{ 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0 }},
        {{ 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0 }},
        {{ 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 2, 0, 2 }},
        {{ 2, 0, 2, 0, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0 }},
        {{ 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0 }},
        {{ 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2 }},
        {{ 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2 }},
        {{ 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 2, 0, 0, 0, 2 }},
        {{ 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 0, 2, 2 }},
        {{ 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 2, 2 }},
        {{ 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 2, 4 }}
    }};
    std::array<unsigned long long int, 4> cnt{{ 1, 0, 0, 0 }};
    for (int _ = 0; _ < nbit - 1; ++_) {
        const bool bdL = dL & 1;
        const bool bdR = dR & 1;
        const bool bnL = nL & 1;
        const bool bnR = nR & 1;
        std::array<unsigned long long int, 4> tmp{{ 1, 0, 0, 0 }};
        auto tr = table[(bnR << 3) | (bnL << 2) | (bdR << 1) | (bdL << 0)];
        tmp[0] = tr[0 * 4 + 0] * cnt[0] + tr[0 * 4 + 1] * cnt[1] + tr[0 * 4 + 2] * cnt[2] + tr[0 * 4 + 3] * cnt[3];
        tmp[1] = tr[1 * 4 + 0] * cnt[0] + tr[1 * 4 + 1] * cnt[1] + tr[1 * 4 + 2] * cnt[2] + tr[1 * 4 + 3] * cnt[3];
        tmp[2] = tr[2 * 4 + 0] * cnt[0] + tr[2 * 4 + 1] * cnt[1] + tr[2 * 4 + 2] * cnt[2] + tr[2 * 4 + 3] * cnt[3];
        tmp[3] = tr[3 * 4 + 0] * cnt[0] + tr[3 * 4 + 1] * cnt[1] + tr[3 * 4 + 2] * cnt[2] + tr[3 * 4 + 3] * cnt[3];
        if (tmp[0] + tmp[1] + tmp[2] + tmp[3] == 0)
            return 0;

        for (int i = 0; i < 4; ++i)
            cnt[i] = tmp[i];
        dL >>= 1;
        dR >>= 1;
        nL >>= 1;
        nR >>= 1;
    }
    return 4 * (cnt[0] + cnt[1] + cnt[2] + cnt[3]);
}

long double bct_entry128(uint64_t dL, uint64_t dR, uint64_t nL, uint64_t nR, const int nbit)
{
    const std::vector<std::vector<int>> table = {{
        {{ 4, 2, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0 }},
        {{ 2, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2 }},
        {{ 2, 2, 0, 0, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0 }},
        {{ 2, 0, 0, 0, 2, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2 }},
        {{ 2, 0, 2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2 }},
        {{ 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0 }},
        {{ 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0 }},
        {{ 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 2, 0, 0, 2, 0, 2 }},
        {{ 2, 0, 2, 0, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0 }},
        {{ 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0 }},
        {{ 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2 }},
        {{ 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2 }},
        {{ 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 2, 0, 0, 0, 2 }},
        {{ 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 0, 2, 2 }},
        {{ 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 2, 2 }},
        {{ 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 2, 4 }}
    }};
    std::array<absl::uint128, 4> cnt{{ 1, 0, 0, 0 }};
    for (int _ = 0; _ < nbit - 1; ++_) {
        const bool bdL = dL & 1;
        const bool bdR = dR & 1;
        const bool bnL = nL & 1;
        const bool bnR = nR & 1;
        std::array<absl::uint128, 4> tmp{{ 1, 0, 0, 0 }};
        auto tr = table[(bnR << 3) | (bnL << 2) | (bdR << 1) | (bdL << 0)];
        tmp[0] = tr[0 * 4 + 0] * cnt[0] + tr[0 * 4 + 1] * cnt[1] + tr[0 * 4 + 2] * cnt[2] + tr[0 * 4 + 3] * cnt[3];
        tmp[1] = tr[1 * 4 + 0] * cnt[0] + tr[1 * 4 + 1] * cnt[1] + tr[1 * 4 + 2] * cnt[2] + tr[1 * 4 + 3] * cnt[3];
        tmp[2] = tr[2 * 4 + 0] * cnt[0] + tr[2 * 4 + 1] * cnt[1] + tr[2 * 4 + 2] * cnt[2] + tr[2 * 4 + 3] * cnt[3];
        tmp[3] = tr[3 * 4 + 0] * cnt[0] + tr[3 * 4 + 1] * cnt[1] + tr[3 * 4 + 2] * cnt[2] + tr[3 * 4 + 3] * cnt[3];
        if (tmp[0] + tmp[1] + tmp[2] + tmp[3] == 0)
            return 0;

        for (int i = 0; i < 4; ++i)
            cnt[i] = tmp[i];
        dL >>= 1;
        dR >>= 1;
        nL >>= 1;
        nR >>= 1;
    }

    absl::uint128 dp_sum = cnt[0] + cnt[1] + cnt[2] + cnt[3];

    // dp_sum * 4 / 2**(2 * nbit)
    uint64_t pt = static_cast<uint64_t>(1) << (nbit - 1);
    const auto dpDivNbit = static_cast<uint64_t>(dp_sum / pt);
    return dpDivNbit * 1.0 / pt;
}

static inline unsigned char lbct_transfer(const unsigned char state, const bool l, const bool r, const bool dL, const bool dR, const bool nL, const bool nR, const bool nLL)
{
    const bool c1 = (state >> 0) & 1;
    const bool b1 = (state >> 1) & 1;
    const bool c2 = (state >> 2) & 1;
    const bool b2 = (state >> 3) & 1;
    const bool c3 = (state >> 4) & 1;
    const bool tmp1 = carry(l, r, c1);
    const bool tmp2 = borrow(l ^ r ^ c1 ^ nL, r ^ nR, b1);
    const bool tmp3 = carry(l ^ dL, r ^ dR, c2);
    const bool tmp4 = borrow(l ^ dL ^ r ^ dR ^ c2 ^ nL, r ^ dR ^ nR, b2);
    const bool tmp5 = carry(l ^ nLL, r ^ nR, c3);

    const unsigned char next_state = (tmp5 << 4) ^ (tmp4 << 3) ^ (tmp3 << 2) ^ (tmp2 << 1) ^ (tmp1 << 0);
    if ( (next_state & 0b10000) != 0 )
        return next_state ^ 0b11111;
    return next_state;
}

unsigned long long int lbct_entry(unsigned int dL, unsigned int dR, unsigned int nL, unsigned int nR, unsigned int nLL, const int nbit)
{
    const std::array<unsigned char, 8> valid_state{{ 0b00000, 0b00011, 0b00101, 0b00110, 0b01001, 0b01010, 0b01100, 0b01111 }};
    const std::array<int, 16> state2index{{
        0, -1, -1, 1, -1, 2, 3, -1, -1, 4, 5, -1, 6, -1, -1, 7
    }};
    const std::array<bool, 16> isValid{{
        1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1
    }};
    std::array<unsigned long long int, 8> dp{{ 1, 0, 0, 0, 0, 0, 0, 0 }};
    for (int i = 0; i < nbit - 1; ++i) {
        std::array<unsigned long long int, 8> dp_t{{ 0, 0, 0, 0, 0, 0, 0, 0 }};
        for (int state = 0; state < 8; ++state) {
            if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 4)&1) ^ (nLL&1) ^ (nR&1) ^ (nL&1) ) != 0 )
                continue;
            for (int xy = 0; xy < 0b11 + 1; ++xy) {
                const bool x = (xy >> 1) & 1;
                const bool y = (xy >> 0) & 1;
                const unsigned char next_state = lbct_transfer(valid_state[state], x, y, dL&1, dR&1, nL&1, nR&1, nLL&1);
                if (!isValid[next_state]) continue;
                dp_t[state2index[next_state]] += dp[state];
            }
        }
        uint64_t tmpSum = 0;
        for (int state = 0; state < 8; ++state) {
            dp[state] = dp_t[state];
            tmpSum += dp_t[state];
        }
        if (tmpSum == 0) return 0;
        dL = dL >> 1;
        dR = dR >> 1;
        nL = nL >> 1;
        nR = nR >> 1;
        nLL = nLL >> 1;
    }

    unsigned long long int dp_sum = 0;
    for (int state = 0; state < 8; ++state) {
        if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 4)&1) ^ (nLL&1) ^ (nR&1) ^ (nL&1) ) != 0 )
            dp[state] = 0;
        dp_sum += dp[state];
    }
    return 4 * dp_sum;
}

long double lbct_entry128(uint64_t dL, uint64_t dR, uint64_t nL, uint64_t nR, uint64_t nLL, const int nbit)
{
    const std::array<unsigned char, 8> valid_state{{ 0b00000, 0b00011, 0b00101, 0b00110, 0b01001, 0b01010, 0b01100, 0b01111 }};
    const std::array<int, 16> state2index{{
        0, -1, -1, 1, -1, 2, 3, -1, -1, 4, 5, -1, 6, -1, -1, 7
    }};
    const std::array<bool, 16> isValid{{
        1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1
    }};
    std::array<absl::uint128, 8> dp{{ 1, 0, 0, 0, 0, 0, 0, 0 }};
    for (int i = 0; i < nbit - 1; ++i) {
        std::array<absl::uint128, 8> dp_t{{ 0, 0, 0, 0, 0, 0, 0, 0 }};
        for (int state = 0; state < 8; ++state) {
            if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 4)&1) ^ (nLL&1) ^ (nR&1) ^ (nL&1) ) != 0 )
                continue;
            for (int xy = 0; xy < 0b11 + 1; ++xy) {
                const bool x = (xy >> 1) & 1;
                const bool y = (xy >> 0) & 1;
                const unsigned char next_state = lbct_transfer(valid_state[state], x, y, dL&1, dR&1, nL&1, nR&1, nLL&1);
                if (!isValid[next_state]) continue;
                dp_t[state2index[next_state]] += dp[state];
            }
        }
        absl::uint128 tmpSum = 0;
        for (int state = 0; state < 8; ++state) {
            dp[state] = dp_t[state];
            tmpSum += dp_t[state];
        }
        if (tmpSum == 0) return 0;
        dL = dL >> 1;
        dR = dR >> 1;
        nL = nL >> 1;
        nR = nR >> 1;
        nLL = nLL >> 1;
    }

    absl::uint128 dp_sum = 0;
    for (int state = 0; state < 8; ++state) {
        if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 4)&1) ^ (nLL&1) ^ (nR&1) ^ (nL&1) ) != 0 )
            dp[state] = 0;
        dp_sum += dp[state];
    }

    // dp_sum * 4 / 2**(2 * nbit)
    uint64_t pt = static_cast<uint64_t>(1) << (nbit - 1);
    const auto dpDivNbit = static_cast<uint64_t>(dp_sum / pt);
    return dpDivNbit * 1.0 / pt;
}

static inline unsigned char ubct_transfer(const unsigned char state, const bool l, const bool r, const bool dL, const bool dR, const bool nL, const bool nR, const bool dLL)
{
    const bool c1 = (state >> 0) & 1;
    const bool b1 = (state >> 1) & 1;
    const bool c2 = (state >> 2) & 1;
    const bool b2 = (state >> 3) & 1;
    const bool tmp1 = carry(l, r, c1);
    const bool tmp2 = borrow(l ^ r ^ c1 ^ nL, r ^ nR, b1);
    const bool tmp3 = carry(l ^ dL, r ^ dR, c2);
    const bool tmp4 = borrow(l ^ dL ^ r ^ dR ^ c2 ^ nL, r ^ dR ^ nR, b2);

    const unsigned char next_state = (tmp4 << 3) ^ (tmp3 << 2) ^ (tmp2 << 1) ^ (tmp1 << 0);
    if ( (next_state & 0b1000) != 0 )
        return next_state ^ 0b1111;
    return next_state;
}

unsigned long long int ubct_entry(unsigned int dL, unsigned int dR, unsigned int nL, unsigned int nR, unsigned int dLL, const int nbit)
{
    const std::array<unsigned char, 4> valid_state{{ 0b0000, 0b0011, 0b0101, 0b0110 }};
    const std::array<int, 8> state2index{{
        0, -1, -1, 1, -1, 2, 3, -1
    }};
    const std::array<bool, 8> isValid{{
        1, 0, 0, 1, 0, 1, 1, 0
    }};
    std::array<unsigned long long int, 4> dp{{ 1, 0, 0, 0 }};
    for (int i = 0; i < nbit - 1; ++i) {
        std::array<unsigned long long int, 4> dp_t{{ 0, 0, 0, 0 }};
        for (int state = 0; state < 4; ++state) {
            if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 2)&1) ^ (dLL&1) ^ (dR&1) ^ (dL&1) ) != 0 )
                continue;
            for (int xy = 0; xy < 0b11 + 1; ++xy) {
                const bool x = (xy >> 1) & 1;
                const bool y = (xy >> 0) & 1;
                const unsigned char next_state = ubct_transfer(valid_state[state], x, y, dL&1, dR&1, nL&1, nR&1, dLL&1);
                if (!isValid[next_state]) continue;
                dp_t[state2index[next_state]] += dp[state];
            }
        }
        uint64_t tmpSum = 0;
        for (int state = 0; state < 4; ++state) {
            dp[state] = dp_t[state];
            tmpSum += dp_t[state];
        }
        if (tmpSum == 0) return 0;
        dL = dL >> 1;
        dR = dR >> 1;
        nL = nL >> 1;
        nR = nR >> 1;
        dLL = dLL >> 1;
    }

    unsigned long long int dp_sum = 0;
    for (int state = 0; state < 4; ++state) {
        if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 2)&1) ^ (dLL&1) ^ (dR&1) ^ (dL&1) ) != 0 )
            dp[state] = 0;
        dp_sum += dp[state];
    }
    return 4 * dp_sum;
}

long double ubct_entry128(uint64_t dL, uint64_t dR, uint64_t nL, uint64_t nR, uint64_t dLL, const int nbit)
{
    const std::array<unsigned char, 4> valid_state{{ 0b0000, 0b0011, 0b0101, 0b0110 }};
    const std::array<int, 8> state2index{{
        0, -1, -1, 1, -1, 2, 3, -1
    }};
    const std::array<bool, 8> isValid{{
        1, 0, 0, 1, 0, 1, 1, 0
    }};
    std::array<absl::uint128, 4> dp{{ 1, 0, 0, 0 }};
    for (int i = 0; i < nbit - 1; ++i) {
        std::array<absl::uint128, 4> dp_t{{ 0, 0, 0, 0 }};
        for (int state = 0; state < 4; ++state) {
            if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 2)&1) ^ (dLL&1) ^ (dR&1) ^ (dL&1) ) != 0 )
                continue;
            for (int xy = 0; xy < 0b11 + 1; ++xy) {
                const bool x = (xy >> 1) & 1;
                const bool y = (xy >> 0) & 1;
                const unsigned char next_state = ubct_transfer(valid_state[state], x, y, dL&1, dR&1, nL&1, nR&1, dLL&1);
                if (!isValid[next_state]) continue;
                dp_t[state2index[next_state]] += dp[state];
            }
        }
        absl::uint128 tmpSum = 0;
        for (int state = 0; state < 4; ++state) {
            dp[state] = dp_t[state];
            tmpSum += dp_t[state];
        }
        if (tmpSum == 0) return 0;
        dL = dL >> 1;
        dR = dR >> 1;
        nL = nL >> 1;
        nR = nR >> 1;
        dLL = dLL >> 1;
    }

    absl::uint128 dp_sum = 0;
    for (int state = 0; state < 4; ++state) {
        if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 2)&1) ^ (dLL&1) ^ (dR&1) ^ (dL&1) ) != 0 )
            dp[state] = 0;
        dp_sum += dp[state];
    }

    // dp_sum * 4 / 2**(2 * nbit)
    uint64_t pt = static_cast<uint64_t>(1) << (nbit - 1);
    const auto dpDivNbit = static_cast<uint64_t>(dp_sum / pt);
    return dpDivNbit * 1.0 / pt;
}

static inline unsigned char ebct_transfer(const unsigned char state, const bool l, const bool r, const bool dL, const bool dR, const bool nL, const bool nR, const bool dLL, const bool nLL)
{
    const bool c1 = (state >> 0) & 1;
    const bool b1 = (state >> 1) & 1;
    const bool c2 = (state >> 2) & 1;
    const bool b2 = (state >> 3) & 1;
    const bool c3 = (state >> 4) & 1;
    const bool tmp1 = carry(l, r, c1);
    const bool tmp2 = borrow(l ^ r ^ c1 ^ nL, r ^ nR, b1);
    const bool tmp3 = carry(l ^ dL, r ^ dR, c2);
    const bool tmp4 = borrow(l ^ dL ^ r ^ dR ^ c2 ^ nL, r ^ dR ^ nR, b2);
    const bool tmp5 = carry(l ^ nLL, r ^ nR, c3);

    const unsigned char next_state = (tmp5 << 4) ^ (tmp4 << 3) ^ (tmp3 << 2) ^ (tmp2 << 1) ^ (tmp1 << 0);
    if ( (next_state & 0b10000) != 0 )
        return next_state ^ 0b11111;
    return next_state;
}

unsigned long long int ebct_entry(unsigned int dL, unsigned int dR, unsigned int nL, unsigned int nR, unsigned int dLL, unsigned int nLL, const int nbit)
{
    const std::array<unsigned char, 8> valid_state{{ 0b00000, 0b00011, 0b00101, 0b00110, 0b01001, 0b01010, 0b01100, 0b01111 }};
    const std::array<int, 16> state2index{{
        0, -1, -1, 1, -1, 2, 3, -1, -1, 4, 5, -1, 6, -1, -1, 7
    }};
    const std::array<bool, 16> isValid{{
        1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1
    }};
    std::array<unsigned long long int, 8> dp{{ 1, 0, 0, 0, 0, 0, 0, 0 }};
    for (int i = 0; i < nbit - 1; ++i) {
        std::array<unsigned long long int, 8> dp_t{{ 0, 0, 0, 0, 0, 0, 0, 0 }};
        for (int state = 0; state < 8; ++state) {
            if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 4)&1) ^ (nLL&1) ^ (nR&1) ^ (nL&1) ) != 0 )
                continue;
            if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 2)&1) ^ (dLL&1) ^ (dR&1) ^ (dL&1) ) != 0 )
                continue;
            for (int xy = 0; xy < 0b11 + 1; ++xy) {
                const bool x = (xy >> 1) & 1;
                const bool y = (xy >> 0) & 1;
                const unsigned char next_state = ebct_transfer(valid_state[state], x, y, dL&1, dR&1, nL&1, nR&1, dLL&1, nLL&1);
                if (!isValid[next_state]) continue;
                dp_t[state2index[next_state]] += dp[state];
            }
        }
        uint64_t tmpSum = 0;
        for (int state = 0; state < 8; ++state) {
            dp[state] = dp_t[state];
            tmpSum += dp_t[state];
        }
        if (tmpSum == 0) return 0;
        dL = dL >> 1;
        dR = dR >> 1;
        nL = nL >> 1;
        nR = nR >> 1;
        dLL = dLL >> 1;
        nLL = nLL >> 1;
    }

    unsigned long long int dp_sum = 0;
    for (int state = 0; state < 8; ++state) {
        if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 4)&1) ^ (nLL&1) ^ (nR&1) ^ (nL&1) ) != 0 )
            dp[state] = 0;
        if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 2)&1) ^ (dLL&1) ^ (dR&1) ^ (dL&1) ) != 0 )
            dp[state] = 0;
        dp_sum += dp[state];
    }
    return 4 * dp_sum;
}

long double ebct_entry128(uint64_t dL, uint64_t dR, uint64_t nL, uint64_t nR, uint64_t dLL, uint64_t nLL, const int nbit)
{
    const std::array<unsigned char, 8> valid_state{{ 0b00000, 0b00011, 0b00101, 0b00110, 0b01001, 0b01010, 0b01100, 0b01111 }};
    const std::array<int, 16> state2index{{
        0, -1, -1, 1, -1, 2, 3, -1, -1, 4, 5, -1, 6, -1, -1, 7
    }};
    const std::array<bool, 16> isValid{{
        1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1
    }};
    std::array<absl::uint128, 8> dp{{ 1, 0, 0, 0, 0, 0, 0, 0 }};
    for (int i = 0; i < nbit - 1; ++i) {
        std::array<absl::uint128, 8> dp_t{{ 0, 0, 0, 0, 0, 0, 0, 0 }};
        for (int state = 0; state < 8; ++state) {
            if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 4)&1) ^ (nLL&1) ^ (nR&1) ^ (nL&1) ) != 0 )
                continue;
            if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 2)&1) ^ (dLL&1) ^ (dR&1) ^ (dL&1) ) != 0 )
                continue;
            for (int xy = 0; xy < 0b11 + 1; ++xy) {
                const bool x = (xy >> 1) & 1;
                const bool y = (xy >> 0) & 1;
                const unsigned char next_state = ebct_transfer(valid_state[state], x, y, dL&1, dR&1, nL&1, nR&1, dLL&1, nLL&1);
                if (!isValid[next_state]) continue;
                dp_t[state2index[next_state]] += dp[state];
            }
        }
        absl::uint128 tmpSum = 0;
        for (int state = 0; state < 8; ++state) {
            dp[state] = dp_t[state];
            tmpSum += dp_t[state];
        }
        if (tmpSum == 0) return 0;
        dL = dL >> 1;
        dR = dR >> 1;
        nL = nL >> 1;
        nR = nR >> 1;
        dLL = dLL >> 1;
        nLL = nLL >> 1;
    }

    absl::uint128 dp_sum = 0;
    for (int state = 0; state < 8; ++state) {
        if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 4)&1) ^ (nLL&1) ^ (nR&1) ^ (nL&1) ) != 0 )
            dp[state] = 0;
        if ( ( ((valid_state[state] >> 0)&1) ^ ((valid_state[state] >> 2)&1) ^ (dLL&1) ^ (dR&1) ^ (dL&1) ) != 0 )
            dp[state] = 0;
        dp_sum += dp[state];
    }

    // dp_sum * 4 / 2**(2 * nbit)
    uint64_t pt = static_cast<uint64_t>(1) << (nbit - 1);
    const auto dpDivNbit = static_cast<uint64_t>(dp_sum / pt);
    return dpDivNbit * 1.0 / pt;
}
