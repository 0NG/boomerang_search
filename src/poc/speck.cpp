#include <iostream>
#include <iomanip>
#include <cstring>
#include <string>
#include <random>
#include <array>
#include <unordered_map>
#include <cmath>
#include <queue>

using std::cin;
using std::cout;
using std::endl;

static void info(std::string s)
{
    return;
    static int steps;
    cout << "[" << steps << "] " << s << endl;
    ++steps;
    return;
}

template<int textSize>
void printx(const unsigned char s[textSize])
{
    std::cout << std::hex;
    for (int i = 0; i < textSize; ++i) {
        if (i % 4 == 0) std::cout << "| ";
        std::cout << std::setw(2) << std::setfill('0') << static_cast<unsigned int>(s[i]) << ' ';
    }
    std::cout << std::dec;
    std::cout << "| ";
    return;
}

template<int branchSize>
static inline uint64_t ror(uint64_t x, const int rn = 0)
{
    const uint64_t mask = ((uint64_t)(1) << branchSize) - 1;
    return ((x << (branchSize - rn)) | (x >> rn)) & mask;
}

template<int branchSize>
static inline uint64_t rol(uint64_t x, const int rn = 0)
{
    const uint64_t mask = ((uint64_t)(1) << branchSize) - 1;
    return ((x << rn) | (x >> (branchSize - rn))) & mask;
}

template<int ROUND, int branchSize, int KEYSIZE>
static void key_schedule(uint64_t roundkeys[], const uint64_t key[])
{
    constexpr int alpha = 7 + (branchSize != 16);
    constexpr int beta = 2 + (branchSize != 16);
    const uint64_t mask = ((uint64_t)(1) << branchSize) - 1;

    std::queue<uint64_t> li;
    roundkeys[0] = key[0] & mask;
    uint64_t ki = key[0] & mask;
    for (int i = 1; i < KEYSIZE; ++i) li.push(key[i] & mask);

    for (int i = 1; i < ROUND; ++i) {
        uint64_t l = li.front();
        l = ror<branchSize>(l, alpha);
        const uint64_t nextL = ((ki + l) & mask) ^ (i - 1);

        ki = rol<branchSize>(ki, beta) ^ nextL;
        li.push(nextL);
        roundkeys[i] = ki;
    }
    return;
}

template<int ROUND, int branchSize>
static void speck_encrypt(uint64_t ciphertext[2], const uint64_t plaintext[2], const uint64_t roundkeys[])
{
    constexpr int alpha = 7 + (branchSize != 16);
    constexpr int beta = 2 + (branchSize != 16);
    const uint64_t mask = ((uint64_t)(1) << branchSize) - 1;

    uint64_t l = plaintext[0];
    uint64_t r = plaintext[1];
    for (int i = 0; i < ROUND; ++i) {
        l = ror<branchSize>(l, alpha);
        l = (l + r) & mask;

        l ^= roundkeys[i];

        r = rol<branchSize>(r, beta);
        r = l ^ r;
    }
    ciphertext[0] = l;
    ciphertext[1] = r;

    return;
}

template<int ROUND, int branchSize>
static void speck_decrypt(uint64_t plaintext[2], const uint64_t ciphertext[2], const uint64_t roundkeys[ROUND])
{
    constexpr int alpha = 7 + (branchSize != 16);
    constexpr int beta = 2 + (branchSize != 16);
    const uint64_t mask = ((uint64_t)(1) << branchSize) - 1;

    uint64_t l = ciphertext[0];
    uint64_t r = ciphertext[1];
    for (int i = ROUND - 1; i >= 0; --i) {
        r = l ^ r;
        r = ror<branchSize>(r, beta);

        l ^= roundkeys[i];

        l = (l - r) & mask;
        l = rol<branchSize>(l, alpha);
    }
    plaintext[0] = l;
    plaintext[1] = r;
    return;
}

template<int ROUND>
static void speck32_enc(unsigned char ciphertext[4], const unsigned char plaintext[4], const uint64_t roundkeys[])
{
    uint64_t plain[2];
    uint64_t cipher[2];

    const auto pll = reinterpret_cast<const unsigned short*>(plaintext);
    plain[0] = pll[0];
    plain[1] = pll[1];

    speck_encrypt<ROUND, 16>(cipher, plain, roundkeys);

    const auto cll = reinterpret_cast<unsigned short*>(ciphertext);
    cll[0] = cipher[0];
    cll[1] = cipher[1];
    return;
}

template<int ROUND>
static void speck32_dec(unsigned char plaintext[4], const unsigned char ciphertext[4], const uint64_t roundkeys[])
{
    uint64_t plain[2];
    uint64_t cipher[2];

    const auto cll = reinterpret_cast<const unsigned short*>(ciphertext);
    cipher[0] = cll[0];
    cipher[1] = cll[1];

    speck_decrypt<ROUND, 16>(plain, cipher, roundkeys);

    const auto pll = reinterpret_cast<unsigned short*>(plaintext);
    pll[0] = plain[0];
    pll[1] = plain[1];
    return;
}

template<int ROUND>
static unsigned int speck32_enc(const unsigned int plaintext, const uint64_t roundkeys[])
{
    uint64_t plain[2];
    uint64_t cipher[2];

    plain[0] = plaintext & 0xffff;
    plain[1] = plaintext >> 16;

    speck_encrypt<ROUND, 16>(cipher, plain, roundkeys);

    return (cipher[1] << 16) | cipher[0];
}

template<int ROUND>
static unsigned int speck32_dec(const unsigned int ciphertext, const uint64_t roundkeys[])
{
    uint64_t plain[2];
    uint64_t cipher[2];

    cipher[0] = ciphertext & 0xffff;
    cipher[1] = ciphertext >> 16;

    speck_decrypt<ROUND, 16>(plain, cipher, roundkeys);

    return (plain[1] << 16) | plain[0];
}


static int verify32()
{
    constexpr int rounds = 10;
    constexpr unsigned int inputDiff = 0x2800 + (0x0010 << 16);
    constexpr unsigned int outputDiff = 0x8102 + (0x8108 << 16);
    //constexpr unsigned int inputDiff = 0x2040 + (0x0040 << 16);
    //constexpr unsigned int outputDiff = 0xa840 + (0x0800 << 16);

    constexpr unsigned int pcnt = 1 << 28;

    uint64_t key[rounds];

    std::random_device rd;
    std::default_random_engine randomgen(rd());
    std::uniform_int_distribution<unsigned int> dist(0, (1 << 16) - 1);
    std::uniform_int_distribution<unsigned int> dist32(0, 0xffffffff);

    uint64_t masterkey[4];
    for (int i = 0; i < 4; ++i) masterkey[i] = dist(randomgen);
    key_schedule<rounds, 32 / 2, 2>(key, masterkey);
    std::unordered_map<unsigned int, bool> isOccur;

    int cnt = 0;
    for (unsigned int i = 0; i < pcnt; ++i) {
        unsigned int ptmp1;// = static_cast<unsigned short>(dist(randomgen)) ^ (static_cast<unsigned short>(dist(randomgen)) << 16);
        while (true) {
            //ptmp1 = static_cast<unsigned short>(dist(randomgen)) ^ (static_cast<unsigned short>(dist(randomgen)) << 16);
            ptmp1 = dist32(randomgen);
            const auto lup = isOccur.find(ptmp1);
            if (lup == isOccur.end()) {
                isOccur[ptmp1] = true;
                break;
            }
        }
        //const unsigned int ptmp1 = dist32(randomgen);

        const unsigned int ptmp2 = ptmp1 ^ inputDiff;
        const unsigned int ctmp1 = speck32_enc<rounds>(ptmp1, key) ^ outputDiff;
        const unsigned int ctmp2 = speck32_enc<rounds>(ptmp2, key) ^ outputDiff;

        const unsigned int tmp1 = speck32_dec<rounds>(ctmp1, key);
        const unsigned int tmp2 = speck32_dec<rounds>(ctmp2, key);

        if ((tmp1 ^ tmp2) == inputDiff) {
            ++cnt;
        }
    }

    //cout << cnt << " / " << pcnt << " = " << "2^{" << log2(cnt * 1.0 / pcnt) << "}" << endl;

    return cnt;
}

static int verify32_diff()
{
    constexpr int rounds = 10;
    constexpr unsigned int inputDiff = 0x2040 + (0x0040 << 16);
    constexpr unsigned int outputDiff = 0xa840 + (0x0800 << 16);

    constexpr unsigned int pcnt = 1 << 28;

    uint64_t key[rounds];

    std::random_device rd;
    std::default_random_engine randomgen(rd());
    std::uniform_int_distribution<unsigned int> dist(0, (1 << 16) - 1);
    std::uniform_int_distribution<unsigned int> dist32(0, 0xffffffff);

    uint64_t masterkey[4];
    for (int i = 0; i < 4; ++i) masterkey[i] = dist(randomgen);
    key_schedule<rounds, 32 / 2, 2>(key, masterkey);
    std::unordered_map<unsigned int, bool> isOccur;

    int cnt = 0;
    for (unsigned int i = 0; i < pcnt; ++i) {
        unsigned int ptmp1;
        while (true) {
            ptmp1 = dist32(randomgen);
            const auto lup = isOccur.find(ptmp1);
            if (lup == isOccur.end()) {
                isOccur[ptmp1] = true;
                break;
            }
        }

        const unsigned int ptmp2 = ptmp1 ^ inputDiff;
        const unsigned int ctmp1 = speck32_enc<rounds>(ptmp1, key);
        const unsigned int ctmp2 = speck32_enc<rounds>(ptmp2, key);

        if ((ctmp1 ^ ctmp2) == outputDiff) {
            ++cnt;
        }
    }

    //cout << cnt << " / " << pcnt << " = " << "2^{" << log2(cnt * 1.0 / pcnt) << "}" << endl;

    return cnt;
}

int main()
{
    int total = 0;
    int t = 0;
    while (1) {
//        const auto cnt = verify32_diff();
        const auto cnt = verify32();
        total += cnt;
        ++t;
        cout << "times: " << t << ", total: " << total << endl;
    }
    return 0;
}
