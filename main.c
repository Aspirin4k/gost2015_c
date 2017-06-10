#include <stdio.h>
#include <stdlib.h>

#define BLOCK_SIZE 16
#define GALUA_MODULO 451

static const unsigned char MASTER_KEY[32] = {
    0x88, 0x99, 0xaa, 0xbb, 0xcc,
    0xdd, 0xee, 0xff, 0x00, 0x11,
    0x22, 0x33, 0x44, 0x55, 0x66,
    0x77, 0xfe, 0xdc, 0xba, 0x98,
    0x76, 0x54, 0x32, 0x10, 0x01,
    0x23, 0x45, 0x67, 0x89, 0xab,
    0xcd, 0xef
};

static unsigned char SESSION_KEYS[10][16];

// S-block
static const unsigned char S[256] = {
    252, 238, 221,  17, 207, 110,  49,  22, 251,
    196, 250, 218,  35, 197,   4,  77, 233, 119,
    240, 219, 147,  46, 153, 186,  23,  54, 241,
    187,  20, 205,  95, 193, 249,  24, 101,  90,
    226,  92, 239,  33, 129,  28,  60,  66, 139,
      1, 142,  79,   5, 132,   2, 174, 227, 106,
    143, 160,   6,  11, 237, 152, 127, 212, 211,
     31, 235,  52,  44,  81, 234, 200,  72, 171,
    242,  42, 104, 162, 253,  58, 206, 204, 181,
    112,  14,  86,   8,  12, 118,  18, 191, 114,
     19,  71, 156, 183,  93, 135,  21, 161, 150,
     41,  16, 123, 154, 199, 243, 145, 120, 111,
    157, 158, 178, 177,  50, 117,  25,  61, 255,
     53, 138, 126, 109,  84, 198, 128, 195, 189,
     13,  87, 223, 245,  36, 169,  62, 168,  67,
    201, 215, 121, 214, 246, 124,  34, 185,   3,
    224,  15, 236, 222, 122, 148, 176, 188, 220,
    232,  40,  80,  78,  51,  10,  74, 167, 151,
     96, 115,  30,   0,  98,  68,  26, 184,  56,
    130, 100, 159,  38,  65, 173,  69,  70, 146,
     39,  94,  85,  47, 140, 163, 165, 125, 105,
    213, 149,  59,   7,  88, 179,  64, 134, 172,
     29, 247,  48,  55, 107, 228, 136, 217, 231,
    137, 225,  27, 131,  73,  76,  63, 248, 254,
    141,  83, 170, 144, 202, 216, 133,  97,  32,
    113, 103, 164,  45,  43,   9,  91, 203, 155,
     37, 208, 190, 229, 108,  82,  89, 166, 116,
    210, 230, 244, 180, 192, 209, 102, 175, 194,
     57,  75,  99, 182
};

static void non_linear(unsigned char *blocks);
static void non_linear_reverse(unsigned char *blocks);
static void linear_R(unsigned char *blocks);
static void linear_L(unsigned char *blocks);
static unsigned char phi(unsigned char *blocks);
static unsigned char sum_over_Galua(unsigned char a, unsigned char b);
static unsigned char mult_over_Galua(unsigned char a, unsigned char b);
static unsigned char modulo_over_Galua(unsigned short a);
static void xor(unsigned char *blocks, unsigned char *key);
static void key_deploy();
static void F(unsigned char *key, unsigned char *a, unsigned char *b);
static void Encode(unsigned char *a);

/*
*   Non linear modification. S-block in this case.
*/
static void non_linear(unsigned char *blocks)
{
    for (unsigned char i=0; i<BLOCK_SIZE; i++)
        blocks[i] = S[blocks[i]];
}

/*
*   Reverse modification for decrypt
*/
static void non_linear_reverse(unsigned char *blocks)
{
    for (unsigned char i=0; i<BLOCK_SIZE; i++)
    {
        int j=0;
        while (S[j] != blocks[i]) j++;
        blocks[i]=j;
    }
}

/*
*   Linear R modification (Operations over Galua)
*/
static void linear_R(unsigned char *blocks)
{
    unsigned char buffer = phi(blocks);

    for (unsigned char i = 15; i >= 1; i--)
        blocks[i] = blocks[i-1];
    blocks[0] = buffer;
}

/*
*   Reverse linear modification for decrypt
*/
static void linear_R_reverse(unsigned char *blocks)
{
    unsigned char buffer = blocks[0];

    for (unsigned char i = 1; i < BLOCK_SIZE; i++)
        blocks[i-1] = blocks[i];
    blocks[15] = buffer;
    blocks[15] = phi(blocks);
}

/*
*   Linear L modification, which is just R x 16 times
*/
static void linear_L(unsigned char *blocks)
{
    for (unsigned char i=0; i<16; i++)
        linear_R(blocks);
}

static void linear_L_reverse(unsigned char *blocks)
{
    for (unsigned char i=0; i<16; i++)
        linear_R_reverse(blocks);
}

/*
*   Phi function, which is part of linear modification
*/
static unsigned char phi(unsigned char *blocks)
{
    return sum_over_Galua(
            sum_over_Galua(
                sum_over_Galua(
                    sum_over_Galua(
                        mult_over_Galua(148, blocks[0]),
                        mult_over_Galua( 32, blocks[1])
                    ),
                    sum_over_Galua(
                        mult_over_Galua(133, blocks[2]),
                        mult_over_Galua( 16, blocks[3])
                    )
                ),
                sum_over_Galua(
                    sum_over_Galua(
                        mult_over_Galua(194, blocks[4]),
                        mult_over_Galua(192, blocks[5])
                    ),
                    sum_over_Galua(
                        mult_over_Galua(  1, blocks[6]),
                        mult_over_Galua(251, blocks[7])
                    )
                )
            ),
            sum_over_Galua(
                sum_over_Galua(
                    sum_over_Galua(
                        mult_over_Galua(  1, blocks[8]),
                        mult_over_Galua(192, blocks[9])
                    ),
                    sum_over_Galua(
                        mult_over_Galua(194, blocks[10]),
                        mult_over_Galua( 16, blocks[11])
                    )
                ),
                sum_over_Galua(
                    sum_over_Galua(
                        mult_over_Galua(133, blocks[12]),
                        mult_over_Galua( 32, blocks[13])
                    ),
                    sum_over_Galua(
                        mult_over_Galua(148, blocks[14]),
                        mult_over_Galua(  1, blocks[15])
                    )
                )
            )
        );
}

/*
*   Sum 2 polynomial over Galua modulo GALUA_MODULO
*/
static unsigned char sum_over_Galua(unsigned char a, unsigned char b)
{
    return a ^ b;
}

/*
*   Multiplies 2 polynomial over Galua modulo GALUA_MODULO
*/
static unsigned char mult_over_Galua(unsigned char a, unsigned char b)
{
    unsigned short result=0;
    for (unsigned char i=0; i<8; i++)
    {
        for (unsigned char j=0; j<8; j++)
        {
            if (((a >> i) & 1) && ((b >> j) & 1))
                result = result ^ (1 << (i + j));
        }
    }
    return modulo_over_Galua(result);
}

/*
*   Takes modulo over Galua
*/
static unsigned char modulo_over_Galua(unsigned short a)
{
    unsigned char most_significant_digit_modulo = 0;
    unsigned char most_significant_digit_a = 0;
    for (unsigned char i=15; (i>=0) && (most_significant_digit_modulo == 0); i--)
        if ((GALUA_MODULO >> i) & 1) most_significant_digit_modulo = i;

    while ((a >> most_significant_digit_modulo) != 0)
    {
        for (unsigned char i=15; (i>=0) && (most_significant_digit_a == 0); i--)
            if ((a >> i) & 1) most_significant_digit_a = i;

        a = (GALUA_MODULO << (most_significant_digit_a - most_significant_digit_modulo)) ^ a;
        most_significant_digit_a = 0;
    }

    return (unsigned char)a;
}

/*
*   Simple xor
*/
static void xor(unsigned char *blocks, unsigned char *key)
{
    for (unsigned char i=0; i < BLOCK_SIZE; i++)
        blocks[i] = blocks[i] ^ key[i];
}

/*
*   Generating session keys
*/
static void key_deploy()
{
    for (unsigned char i=0; i < BLOCK_SIZE; i++)
        SESSION_KEYS[0][i] = MASTER_KEY[i];

    for (unsigned char i=0; i < BLOCK_SIZE; i++)
        SESSION_KEYS[1][i] = MASTER_KEY[BLOCK_SIZE + i];

    unsigned char iterator_consts[BLOCK_SIZE];
    for (unsigned char i=2; i<10; i+=2)
    {
        for (unsigned char j=0; j<BLOCK_SIZE; j++)
            SESSION_KEYS[i][j] = SESSION_KEYS[i-2][j];

        for (unsigned char j=0; j<BLOCK_SIZE; j++)
            SESSION_KEYS[i+1][j] = SESSION_KEYS[i-1][j];

        for (unsigned char j=0; j<8; j++)
        {
            for (unsigned char z=0; z<BLOCK_SIZE-1; z++)
                iterator_consts[z] = 0;
            iterator_consts[15] = 8 * (i/2 - 1) + j + 1;
            linear_L(iterator_consts);
            F(iterator_consts,SESSION_KEYS[i], SESSION_KEYS[i+1]);
        }
    }
}

/*
*   used in key deploy
*/
static void F(unsigned char *key, unsigned char *a, unsigned char *b)
{
    unsigned char buffer[BLOCK_SIZE];
    for (unsigned char i=0; i< BLOCK_SIZE; i++)
        buffer[i] = a[i];

    xor(a, key);
    non_linear(a);
    linear_L(a);
    xor(a, b);

    for (unsigned char i=0; i< BLOCK_SIZE; i++)
        b[i] = buffer[i];
}

/*
*
*/
static void Encode(unsigned char *a)
{

    for (unsigned char i=0; i<9; i++)
    {
        xor(a, SESSION_KEYS[i]);
        non_linear(a);
        linear_L(a);
    }
    xor(a, SESSION_KEYS[9]);
}

static void Decode(unsigned char *a)
{
    for (unsigned char i=0; i<9; i++)
    {
        xor(a, SESSION_KEYS[9-i]);
        linear_L_reverse(a);
        non_linear_reverse(a);
    }

    xor(a, SESSION_KEYS[0]);
}

int main()
{
    key_deploy();
    unsigned char a[32] = {
        0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
        0x77, 0x00, 0xff, 0xee, 0xdd, 0xcc,
        0xbb, 0xaa, 0x99, 0x88
    };

    for (int i=0; i<BLOCK_SIZE; i++)
        printf("%x", a[i]);
    printf("\n");

    Encode(a);

    for (int i=0; i<BLOCK_SIZE; i++)
        printf("%x", a[i]);
    printf("\n");

    Decode(a);
    for (int i=0; i<BLOCK_SIZE; i++)
        printf("%x", a[i]);
    printf("\n");

    return 0;
}
