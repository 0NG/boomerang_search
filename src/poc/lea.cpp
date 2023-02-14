#include <iostream>
#include <iomanip>
#include <cstring>
#include <string>
#include <random>
#include <array>
#include <unordered_map>
#include <cmath>

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

template<int WORDSIZE>
static inline unsigned int ror(unsigned int x, const int rn = 0)
{
    return ((x << (WORDSIZE - rn)) | (x >> rn));
}

template<int WORDSIZE>
static inline unsigned int rol(unsigned int x, const int rn = 0)
{
    return ((x << rn) | (x >> (WORDSIZE - rn)));
}

template<int ROUND>
static void key_schedule(unsigned int roundkeys[ROUND][6], const unsigned char key[16])
{
    constexpr std::array<unsigned int, 8> delta{
        0xc3efe9db, 0x44626b02,
        0x79e27c8a, 0x78df30ec,
        0x715ea49e, 0xc785da0a,
        0xe04ef22a, 0xe5c40957
    };
    constexpr std::array<int, 4> rn{1, 3, 6, 11};

    unsigned int T[4];
    memcpy(T, key, 16);

    for (int i = 0; i < ROUND; ++i) {
        const unsigned int tmp0 = T[0] + rol<32>(delta[i & 0b11], i + 0);
        const unsigned int tmp1 = T[1] + rol<32>(delta[i & 0b11], i + 1);
        const unsigned int tmp2 = T[2] + rol<32>(delta[i & 0b11], i + 2);
        const unsigned int tmp3 = T[3] + rol<32>(delta[i & 0b11], i + 3);

        T[0] = rol<32>(tmp0, rn[0]);
        T[1] = rol<32>(tmp1, rn[1]);
        T[2] = rol<32>(tmp2, rn[2]);
        T[3] = rol<32>(tmp3, rn[3]);

        roundkeys[i][0] = T[0];
        roundkeys[i][1] = T[1];
        roundkeys[i][2] = T[2];
        roundkeys[i][3] = T[1];
        roundkeys[i][4] = T[3];
        roundkeys[i][5] = T[1];
    }
    return;
}

template<int ROUND>
static void lea_encrypt(unsigned char ciphertext[16], const unsigned char plaintext[16], const unsigned int roundkeys[][6])
{
    constexpr std::array<int, 4> rn{0, 9, 32 - 5, 32 - 3};

    unsigned int cipher[4];
    memcpy(cipher, plaintext, 16);

    for (int i = 0; i < ROUND; ++i) {
        const unsigned int tmp3 = (cipher[3] ^ roundkeys[i][5]) + (cipher[2] ^ roundkeys[i][4]);
        const unsigned int tmp2 = (cipher[2] ^ roundkeys[i][3]) + (cipher[1] ^ roundkeys[i][2]);
        const unsigned int tmp1 = (cipher[1] ^ roundkeys[i][1]) + (cipher[0] ^ roundkeys[i][0]);
        cipher[3] = cipher[0];
        cipher[0] = rol<32>(tmp1, rn[1]);
        cipher[1] = rol<32>(tmp2, rn[2]);
        cipher[2] = rol<32>(tmp3, rn[3]);
    }

    memcpy(ciphertext, cipher, 16);
    return;
}

template<int ROUND>
static void lea_decrypt(unsigned char plaintext[16], const unsigned char ciphertext[16], const unsigned int roundkeys[][6])
{
    constexpr std::array<int, 4> rn{0, 9, 32 - 5, 32 - 3};

    unsigned int plain[4];
    memcpy(plain, ciphertext, 16);

    for (int i = ROUND - 1; i >= 0; --i) {
        const unsigned int tmp0 = plain[3];
        const unsigned int tmp1 = ror<32>(plain[0], rn[1]);
        const unsigned int tmp2 = ror<32>(plain[1], rn[2]);
        const unsigned int tmp3 = ror<32>(plain[2], rn[3]);

        const unsigned int ctmp1 = (tmp1 - (tmp0 ^ roundkeys[i][0])) ^ roundkeys[i][1];
        const unsigned int ctmp2 = (tmp2 - (ctmp1 ^ roundkeys[i][2])) ^ roundkeys[i][3];
        const unsigned int ctmp3 = (tmp3 - (ctmp2 ^ roundkeys[i][4])) ^ roundkeys[i][5];

        plain[0] = tmp0;
        plain[1] = ctmp1;
        plain[2] = ctmp2;
        plain[3] = ctmp3;
    }

    memcpy(plaintext, plain, 16);
    return;
}


void boomerang()
{
    constexpr int rounds = 1;
    constexpr int pcnt = 1 << 26;
    constexpr std::array<unsigned int, 4> inputDiff{
        0x28000200, 0x0002a000, 0x00080000, 0x00000001
    };

    constexpr std::array<unsigned int, 4> outputDiff{
        0x80000004, 0x80400004, 0x80400014, 0x80400010
    };

    std::random_device rd;
    std::default_random_engine randomgen(rd());
    std::uniform_int_distribution<int> dist8(0, 0xff);
    std::uniform_int_distribution<unsigned int> dist32(0, 0xffffffff);
    unsigned char secretkey[16];
    for (int i = 0; i < 16; ++i) secretkey[i] = static_cast<unsigned char>(dist8(randomgen));

    unsigned int key[rounds][6];
    key_schedule<rounds>(key, secretkey);

    //for (int i = 0; i < rounds; ++i) {
    //    for (int j = 0; j < 6; ++j) {
    //        key[i][j] = dist32(randomgen);
    //    }
    //}


    cout << endl << "===== test vector =====" << endl;
    unsigned char testvector[] = "!!A testvector!!";
    lea_encrypt<rounds>(testvector, testvector, key);
    printx<16>(testvector); cout << endl;
    lea_decrypt<rounds>(testvector, testvector, key);
    cout << testvector << endl;
    cout << "====== end  test ======" << endl << endl;


    int cnt = 0;
    for (int i = 0; i < pcnt; ++i) {
        unsigned char ptmp1[16];
        unsigned char ptmp2[16];
        const auto ptmp1_uint = reinterpret_cast<unsigned int*>(ptmp1);
        const auto ptmp2_uint = reinterpret_cast<unsigned int*>(ptmp2);
        for (int j = 0; j < 4; ++j) {
            ptmp1_uint[j] = dist32(randomgen);
            ptmp2_uint[j] = ptmp1_uint[j] ^ inputDiff[j];
        }

        unsigned char ctmp1[16];
        unsigned char ctmp2[16];
        const auto ctmp1_uint = reinterpret_cast<unsigned int*>(ctmp1);
        const auto ctmp2_uint = reinterpret_cast<unsigned int*>(ctmp2);
        lea_encrypt<rounds>(ctmp1, ptmp1, key);
        lea_encrypt<rounds>(ctmp2, ptmp2, key);

        unsigned char ctmp3[16];
        unsigned char ctmp4[16];
        const auto ctmp3_uint = reinterpret_cast<unsigned int*>(ctmp3);
        const auto ctmp4_uint = reinterpret_cast<unsigned int*>(ctmp4);
        for (int j = 0; j < 4; ++j) {
            ctmp3_uint[j] = ctmp1_uint[j] ^ outputDiff[j];
            ctmp4_uint[j] = ctmp2_uint[j] ^ outputDiff[j];
        }

        unsigned char ptmp3[16];
        unsigned char ptmp4[16];
        const auto ptmp3_uint = reinterpret_cast<unsigned int*>(ptmp3);
        const auto ptmp4_uint = reinterpret_cast<unsigned int*>(ptmp4);
        lea_decrypt<rounds>(ptmp3, ctmp3, key);
        lea_decrypt<rounds>(ptmp4, ctmp4, key);

        bool isBoom = true;
        for (int j = 0; j < 4; ++j)
            if ((ptmp3_uint[j] ^ ptmp4_uint[j]) != inputDiff[j]) {
                isBoom = false;
                break;
            }
        if (isBoom) ++cnt;
    }

    cout << cnt << " / " << pcnt
         << " = "
         << cnt * 1.0 / pcnt
         << " = "
         << "2^{" << log2(cnt * 1.0 / pcnt) << "}"
         << endl;

    return;
}

int main()
{
    boomerang();
    return 0;
}
